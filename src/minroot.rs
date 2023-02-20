use plonky2::{
    field::{goldilocks_field::GoldilocksField, types::Field},
    gates::noop::NoopGate,
    iop::{
        target::{BoolTarget, Target},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData, CommonCircuitData, VerifierCircuitTarget},
        config::PoseidonGoldilocksConfig,
        proof::{ProofWithPublicInputs, ProofWithPublicInputsTarget},
    },
    recursion::dummy_circuit::cyclic_base_proof,
};

type F = GoldilocksField;
type C = PoseidonGoldilocksConfig;
const D: usize = 2;

pub struct MinRootPI {
    pub x_init: F,
    pub y_init: F,
    pub x_latest: F,
    pub y_latest: F,
    pub counter: F,
}

impl MinRootPI {
    pub fn to_vec(&self) -> Vec<F> {
        vec![
            self.x_init,
            self.y_init,
            self.x_latest,
            self.y_latest,
            self.counter,
        ]
    }
    pub fn from_vec(input: Vec<F>) -> Self {
        Self {
            x_init: input[0],
            y_init: input[1],
            x_latest: input[2],
            y_latest: input[3],
            counter: input[4],
        }
    }
}

pub struct MinRootPITarget {
    pub x_init: Target,
    pub y_init: Target,
    pub x_latest: Target,
    pub y_latest: Target,
    pub counter: Target,
}

impl MinRootPITarget {
    pub fn new(builder: &mut CircuitBuilder<F, D>) -> Self {
        let x_init = builder.add_virtual_target();
        let y_init = builder.add_virtual_target();
        let x_latest = builder.add_virtual_target();
        let y_latest = builder.add_virtual_target();
        let counter = builder.add_virtual_target();
        Self {
            x_init,
            y_init,
            x_latest,
            y_latest,
            counter,
        }
    }
    pub fn to_vec(&self) -> Vec<Target> {
        vec![
            self.x_init,
            self.y_init,
            self.x_latest,
            self.y_latest,
            self.counter,
        ]
    }
    pub fn from_vec(input: Vec<Target>) -> Self {
        Self {
            x_init: input[0],
            y_init: input[1],
            x_latest: input[2],
            y_latest: input[3],
            counter: input[4],
        }
    }
    pub fn connect(&self, builder: &mut CircuitBuilder<F, D>, other: Self) {
        builder.connect(self.x_init, other.x_init);
        builder.connect(self.y_init, other.y_init);
        builder.connect(self.x_latest, other.x_latest);
        builder.connect(self.y_latest, other.y_latest);
        builder.connect(self.counter, other.counter);
    }
}

pub struct MinRootTarget {
    is_initial_step: BoolTarget,
    x_init: Target,
    y_init: Target,
    x_latest: Target,
    y_latest: Target,
    counter: Target,
}

impl MinRootTarget {
    pub fn new(builder: &mut CircuitBuilder<F, D>) -> Self {
        let is_initial_step = builder.add_virtual_bool_target_safe();
        let x_init = builder.add_virtual_target();
        let y_init = builder.add_virtual_target();
        let x_latest = builder.add_virtual_target();
        let y_latest = builder.add_virtual_target();
        let counter = builder.add_virtual_target();
        Self {
            is_initial_step,
            x_init,
            y_init,
            x_latest,
            y_latest,
            counter,
        }
    }
}

pub struct MinRootCircuit {
    pub target: MinRootTarget,
    pub inner_proof: ProofWithPublicInputsTarget<D>,
    pub verifier_data_target: VerifierCircuitTarget,
    pub common_data: CommonCircuitData<F, D>,
    pub cyclic_circuit_data: CircuitData<F, C, D>,
}

impl MinRootCircuit {
    pub fn new(num_iters_per_step: usize) -> Self {
        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let inner_target = MinRootPITarget::new(&mut builder);

        let target = {
            let is_initial_step = builder.add_virtual_bool_target_safe();
            let not_initial_step = builder.not(is_initial_step);
            let one = builder.one();

            // new_counter = counter + 1 if not_initial_step else 1
            let new_counter = builder.mul_add(not_initial_step.target, inner_target.counter, one);

            let mut x = builder.add_virtual_target();
            let mut y = builder.add_virtual_target();

            builder.connect(x, inner_target.x_latest);
            builder.connect(y, inner_target.y_latest);
            for _ in 0..num_iters_per_step {
                let x_plus_y = builder.add(x, y);
                y = x;
                x = builder.exp_u64(x_plus_y, 3689348813882916864);
            }

            let x_new = builder.select(is_initial_step, inner_target.x_init, x);
            let y_new = builder.select(is_initial_step, inner_target.y_init, y);

            MinRootTarget {
                is_initial_step,
                x_init: inner_target.x_init,
                y_init: inner_target.y_init,
                x_latest: x_new,
                y_latest: y_new,
                counter: new_counter,
            }
        };

        // register public input
        let pis_target = MinRootPITarget {
            x_init: target.x_init,
            y_init: target.y_init,
            x_latest: target.x_latest,
            y_latest: target.y_latest,
            counter: target.counter,
        };
        builder.register_public_inputs(&pis_target.to_vec());

        let mut common_data = common_data_for_recursion();
        let verifier_data_target = builder.add_verifier_data_public_inputs();
        common_data.num_public_inputs = builder.num_public_inputs();

        let inner_proof = builder.add_virtual_proof_with_pis(&common_data);

        let inner_proof_pis = MinRootPITarget::from_vec(inner_proof.public_inputs.clone());
        inner_proof_pis.connect(&mut builder, inner_target);

        let not_initial_step = builder.not(target.is_initial_step);
        builder
            .conditionally_verify_cyclic_proof_or_dummy::<C>(
                not_initial_step,
                &inner_proof,
                &common_data,
            )
            .unwrap();
        let cyclic_circuit_data = builder.build::<C>();
        Self {
            target,
            inner_proof,
            verifier_data_target,
            common_data,
            cyclic_circuit_data,
        }
    }

    pub fn set_init_witness(&self, pw: &mut PartialWitness<F>, initial: MinRootPI) {
        let nonzero_public_inputs = initial.to_vec().into_iter().enumerate().collect();
        pw.set_bool_target(self.target.is_initial_step, true);
        pw.set_proof_with_pis_target(
            &self.inner_proof,
            &cyclic_base_proof(
                &self.common_data,
                &self.cyclic_circuit_data.verifier_only,
                nonzero_public_inputs,
            ),
        );
        pw.set_verifier_data_target(
            &self.verifier_data_target,
            &self.cyclic_circuit_data.verifier_only,
        );
    }

    pub fn set_recursive_witness(
        &self,
        pw: &mut PartialWitness<F>,
        proof: &ProofWithPublicInputs<F, C, D>,
    ) {
        pw.set_bool_target(self.target.is_initial_step, false);
        pw.set_proof_with_pis_target::<C, D>(&self.inner_proof, proof);
        pw.set_verifier_data_target(
            &self.verifier_data_target,
            &self.cyclic_circuit_data.verifier_only,
        );
    }

    pub fn prove(&self, pw: PartialWitness<F>) -> anyhow::Result<ProofWithPublicInputs<F, C, D>> {
        let proof = self.cyclic_circuit_data.prove(pw)?;
        Ok(proof)
    }
}

fn common_data_for_recursion() -> CommonCircuitData<F, D> {
    let config = CircuitConfig::standard_recursion_config();
    let builder = CircuitBuilder::<F, D>::new(config);
    let data = builder.build::<C>();
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data = builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    let data = builder.build::<C>();

    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let proof = builder.add_virtual_proof_with_pis(&data.common);
    let verifier_data = builder.add_virtual_verifier_data(data.common.config.fri_config.cap_height);
    builder.verify_proof::<C>(&proof, &verifier_data, &data.common);
    let one = builder.one();
    let _ = builder.exp_u64(one, 42);
    while builder.num_gates() < 1 << COMMON_DATA_DEGREE {
        builder.add_gate(NoopGate, vec![]);
    }
    builder.build::<C>().common
}

const COMMON_DATA_DEGREE: usize = 12;

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn test_min_root() -> anyhow::Result<()> {
        let num_iters_per_step = 1 << 11;
        let num_steps = 100;
        let min_root_circuit = MinRootCircuit::new(num_iters_per_step);

        let initial = MinRootPI {
            x_init: F::from_canonical_usize(42),
            y_init: F::from_canonical_usize(0),
            x_latest: F::from_canonical_usize(0),
            y_latest: F::from_canonical_usize(0),
            counter: F::ZERO,
        };

        let mut pw = PartialWitness::<F>::new();
        min_root_circuit.set_init_witness(&mut pw, initial);
        let mut proof = min_root_circuit.prove(pw)?;

        for i in 1..num_steps {
            let now = Instant::now();
            let mut pw = PartialWitness::new();
            min_root_circuit.set_recursive_witness(&mut pw, &proof);
            proof = min_root_circuit.prove(pw)?;
            println!("prove_step {}, time = {} ms", i, now.elapsed().as_millis());
        }

        Ok(())
    }
}
