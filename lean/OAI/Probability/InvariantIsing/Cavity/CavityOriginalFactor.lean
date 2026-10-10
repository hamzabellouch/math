import OAI.Probability.InvariantIsing.Cavity.CavityPhysicalGibbsSplit
import OAI.Probability.InvariantIsing.Cavity.CavityFullCutoff

namespace OAI

/-! Exact cavity reweighting of the original perturbed spin model.
Both Hamiltonians contain the same Gaussian disorder coordinate. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

def cavityRotationHamiltonian {N m depth : ℕ} (U : Rotation N)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ)
    (z : ℕ → ℝ) (x : Spin N × LabeledLeaf depth) : ℝ :=
  rotatedEnergy eig U x.1 + cylinderField (cavityPerturbationCoefficients U I u depth x) z

lemma cavity_rotation_exp_integrable_ae {N m depth : ℕ}
    (U : Rotation N) (T : LabeledTree depth) (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) :
    ∀ᵐ z ∂gaussianCoordinates, Integrable
      (fun x => Real.exp (cavityRotationHamiltonian U eig I u z x))
      (labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T) := by
  let ν := labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T
  exact cylinder_partition_exp_integrable_ae ν
    (fun x => rotatedEnergy eig U x.1)
    (cavity_bounded_base_exp_integrable ν _ (fun x =>
      Finset.single_le_sum (f := fun σ : Spin N => |rotatedEnergy eig U σ|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ x.1)))
    (cavityPerturbationCoefficients U I u depth)
    (cavityPerturbationCoefficients_sq_le U I u hu)

def cavityOriginalFactor {N n m depth : ℕ}
    (U : Rotation (N+n)) (V : Rotation N)
    (eig : Fin (N+n) → ℝ) (eig₀ : Fin N → ℝ)
    (I : Fin m → Finset (Fin (N+n))) (J : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (z : ℕ → ℝ)
    (x : (Spin N × LabeledLeaf depth) × Spin n) : ℝ :=
  cavityRotationHamiltonian U eig I u z ((cavitySpinLeafSplit N n depth).symm x) -
    cavityRotationHamiltonian V eig₀ J u z x.1

theorem cavity_original_replica_factorization {N n m depth r : ℕ}
    (U : Rotation (N+n)) (V : Rotation N) (T : LabeledTree depth)
    (eig : Fin (N+n) → ℝ) (eig₀ : Fin N → ℝ)
    (I : Fin m → Finset (Fin (N+n))) (J : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2)
    (F : (Fin r → (Spin N × LabeledLeaf depth) × Spin n) → ℝ) :
    ∀ᵐ z ∂gaussianCoordinates,
      referenceReplicaMean
        (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
        (cavityRotationHamiltonian U eig I u z)
        (fun σ => F (fun i => cavitySpinLeafSplit N n depth (σ i))) =
      cavityWeightedReplicaMean
        (((labeledSpinReference depth (uniformSpinPrior N : Measure (Spin N)) T).tilted
          (cavityRotationHamiltonian V eig₀ J u z)).prod (uniformSpinPrior n))
        (fun x => Real.exp (cavityOriginalFactor U V eig eig₀ I J u z x)) F := by
  filter_upwards [cavity_rotation_exp_integrable_ae U T eig I u hu,
    cavity_rotation_exp_integrable_ae V T eig₀ J u hu] with z hU hV
  apply cavity_spin_leaf_replica_split T _ hV _ hU _ _ F
  intro x
  simp only [cavityOriginalFactor, Equiv.symm_apply_apply]
  ring

lemma cavityOriginalFactor_decomposition {N n m depth : ℕ}
    (U : Rotation (N+n)) (V : Rotation N)
    (eig : Fin (N+n) → ℝ) (eig₀ : Fin N → ℝ)
    (I : Fin m → Finset (Fin (N+n))) (J : Fin m → Finset (Fin N))
    (u : ℕ → ℝ) (z : ℕ → ℝ)
    (x : (Spin N × LabeledLeaf depth) × Spin n) :
    cavityOriginalFactor U V eig eig₀ I J u z x =
      (rotatedEnergy eig U ((cavitySpinSplit N n).symm (x.1.1,x.2)) -
        rotatedEnergy eig₀ V x.1.1) +
      cylinderField (cavityPerturbationCoefficients U I u depth
        ((cavitySpinSplit N n).symm (x.1.1,x.2),x.1.2)) z -
      cylinderField (cavityPerturbationCoefficients V J u depth x.1) z := by
  unfold cavityOriginalFactor cavityRotationHamiltonian cavitySpinLeafSplit
  dsimp only [Equiv.coe_fn_symm_mk]
  ring

end InvariantIsing

end

end OAI
