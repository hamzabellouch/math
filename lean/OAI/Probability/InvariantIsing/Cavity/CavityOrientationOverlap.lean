import OAI.Probability.InvariantIsing.Cavity.CavityOrientedProjectors
import OAI.Probability.InvariantIsing.Cavity.CavityRotationArray

namespace OAI

/-! The SO correction changes only coordinate signs in the spectral
basis, so every physical projected overlap and quadratic energy agrees. -/

noncomputable section
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityOrientationLift_eval {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation (cavityOrientationLift hN U) x i =
      (if i=(⟨0,hN⟩ : Fin N) then (U : Matrix (Fin N) (Fin N) ℝ).det else 1)*
        matrixRotation U x i := by
  change ((cavityOrientationSign hN U*(U : Matrix (Fin N) (Fin N) ℝ))*ᵥ x) i = _
  rw [← Matrix.mulVec_mulVec]
  simp only [cavityOrientationSign, Matrix.mulVec_diagonal]
  rfl

lemma cavityOrientationLift_product {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (x y : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    specialRotation (cavityOrientationLift hN U) x i *
      specialRotation (cavityOrientationLift hN U) y i =
        matrixRotation U x i * matrixRotation U y i := by
  rw [cavityOrientationLift_eval, cavityOrientationLift_eval]
  split_ifs
  · rcases orthogonal_det_eq_one_or_neg_one U with h | h <;> rw [h] <;> ring
  · ring

lemma cavityOrientationLift_overlap {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Finset (Fin N)) (σ τ : Spin N) :
    projectedOverlap (specialRotation (cavityOrientationLift hN U)) I σ τ =
      projectedOverlap (matrixRotation U) I σ τ := by
  unfold projectedOverlap
  simp_rw [cavityOrientationLift_product]

lemma cavityOrientationLift_energy {N : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (eig : Fin N → ℝ) (σ : Spin N) :
    rotatedEnergy eig (specialRotation (cavityOrientationLift hN U)) σ =
      rotatedEnergy eig (matrixRotation U) σ := by
  unfold rotatedEnergy
  simp_rw [pow_two, cavityOrientationLift_product]

lemma cavityOrientationLift_jointEntry {N m depth : ℕ} (hN : 0 < N) (U : Orthogonal N)
    (I : Fin m → Finset (Fin N)) (x y : Spin N × IsingPerceptron.LabeledLeaf depth) :
    spectralJointEntry (specialRotation (cavityOrientationLift hN U)) I depth x y =
      spectralJointEntry (matrixRotation U) I depth x y := by
  funext a
  apply Subtype.ext
  refine Fin.lastCases ?_ (fun j => ?_) a
  · rw [spectralJointEntry_tree, spectralJointEntry_tree]
  · rw [spectralJointEntry_spectral, spectralJointEntry_spectral,
      cavityOrientationLift_overlap]

end InvariantIsing

end

end OAI
