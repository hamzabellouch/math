import OAI.Probability.InvariantIsing.Cavity.CavityCutoffMap
import OAI.Probability.InvariantIsing.Cavity.CavityCutoffZero
import OAI.Probability.InvariantIsing.Cavity.CavityOriginalFactor
import OAI.Probability.InvariantIsing.Cavity.CavityDisorderTestComparison

namespace OAI

/-! The cutoff in the original perturbed spin model is exactly the
subtype-prior test occurring in the finite geometric comparison. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Classical

namespace InvariantIsing

lemma cavityJoinedSpin_split {N n : ℕ} (σ : Spin (N+n)) :
    cavityJoinedSpin (cavitySpinSplit N n σ) = σ := by
  change (cavitySpinSplit N n).symm (cavitySpinSplit N n σ) = σ
  exact (cavitySpinSplit N n).symm_apply_apply σ

theorem cavity_original_cutoff_subtype {N n m depth : ℕ}
    (U : Rotation (N+n)) (T : LabeledTree depth)
    (eig : Fin (N+n) → ℝ) (I : Fin m → Finset (Fin (N+n)))
    (v : Fin m → ℝ) (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ)
    (w : Spin N × Spin n → ℝ) (D : ℝ)
    (F : (Fin 2 → (Spin N × Spin n) × LabeledLeaf depth) → ℝ) :
    let ν := ((uniformSpinPrior N : Measure (Spin N)).prod (uniformSpinPrior n)).prod
      (labeledLeafLaw depth T)
    let s := {x : (Spin N × Spin n) × LabeledLeaf depth | w x.1 ≤ D}
    (∫ z, cavityCutoffReplicaMean
      (labeledSpinReference depth (uniformSpinPrior (N+n) : Measure (Spin (N+n))) T)
      (cavityRotationHamiltonian U (diagonalPerturbedEigenvalues eig I v t) I u z)
      {x | w (cavitySpinSplit N n x.1) ≤ D}
      (fun σ => F (fun i => (cavitySpinSplit N n (σ i).1,(σ i).2))) ∂gaussianCoordinates) =
      cavityFullCutoffReplicaMean U I eig v u t w D (subtypeReference ν s)
        (fun σ => F (fun i => (σ i).val)) := by
  intro ν s
  let H := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
    rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U (cavityJoinedSpin x.1)
  let A := fun x : (Spin N × Spin n) × LabeledLeaf depth =>
    cavityPerturbationCoefficients U I u depth (cavityJoinedSpin x.1,x.2)
  have hi : ∀ᵐ z ∂gaussianCoordinates,
      Integrable (fun x => Real.exp (H x + cylinderField (A x) z)) ν := by
    apply cylinder_partition_exp_integrable_ae ν H
    · exact cavity_bounded_base_exp_integrable ν H (fun x =>
        Finset.single_le_sum
          (f := fun σ : Spin (N+n) => |rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ (cavityJoinedSpin x.1)))
    · exact fun x => cavityPerturbationCoefficients_sq_le U I u hu (cavityJoinedSpin x.1,x.2)
  change (∫ z, _ ∂gaussianCoordinates) = ∫ z, _ ∂gaussianCoordinates
  apply integral_congr_ae
  filter_upwards [hi] with z hz
  have he := cavity_spin_cutoff_split T (fun x => H x + cylinderField (A x) z) s F
  have hfun : (fun x : Spin (N+n) × LabeledLeaf depth =>
      H (cavitySpinSplit N n x.1,x.2) + cylinderField (A (cavitySpinSplit N n x.1,x.2)) z) =
      cavityRotationHamiltonian U (diagonalPerturbedEigenvalues eig I v t) I u z := by
    funext x
    simp only [H, A, cavityJoinedSpin_split, cavityRotationHamiltonian]
  rw [hfun] at he
  exact he.trans (cavity_cutoff_replica_subtype_all ν _ hz s
    ((Set.to_countable s).measurableSet) F)

end InvariantIsing

end

end OAI
