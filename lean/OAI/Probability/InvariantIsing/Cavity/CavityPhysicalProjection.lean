import OAI.Probability.InvariantIsing.Cavity.CavitySpinIsometry

namespace OAI

/-! Physical spectral projections and their exact signed-site action. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma cavity_specialRotation_one {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    specialRotation (1 : SpecialOrthogonal N) x = x := by
  ext i
  change ((1 : Matrix (Fin N) (Fin N) ℝ) *ᵥ x.ofLp) i = x i
  simp

lemma cavity_specialRotation_symm {N : ℕ} (U : SpecialOrthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) :
    (specialRotation U).symm x = specialRotation U⁻¹ x := by
  apply (specialRotation U).injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← cavity_specialRotation_mul_apply,
    mul_inv_cancel, cavity_specialRotation_one]

def cavitySpectralProjection {N : ℕ} (U : Rotation N) (I : Finset (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  U.symm (WithLp.toLp 2 (fun k => if k ∈ I then U x k else 0))

lemma cavitySpectralProjection_norm_sq_le {N : ℕ} (U : Rotation N)
    (I : Finset (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    ‖cavitySpectralProjection U I x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [cavitySpectralProjection, U.symm.norm_map, ← U.norm_map x,
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro k _
  change (if k ∈ I then U x k else 0) ^ 2 ≤ (U x k) ^ 2
  split_ifs <;> simp [sq_nonneg]

lemma cavitySpectralProjection_site_sq_le {N : ℕ} (U : Rotation N)
    (I : Finset (Fin N)) (σ : Spin N) (j : Fin N) :
    (cavitySpectralProjection U I (spinVector σ) j) ^ 2 ≤ N := by
  calc
    _ ≤ ‖cavitySpectralProjection U I (spinVector σ)‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ‖spinVector σ‖ ^ 2 := cavitySpectralProjection_norm_sq_le U I _
    _ = N := spinVector_norm_sq σ

lemma cavitySpectralProjection_permutation {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N) (I : Finset (Fin N))
    (σ : Spin N) :
    cavitySpectralProjection (specialRotation (U * (spectralPermutation hN p)⁻¹)) I
      (spinVector (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ)) =
    specialRotation (spectralPermutation hN p)
      (cavitySpectralProjection (specialRotation U) I (spinVector σ)) := by
  apply (specialRotation (U * (spectralPermutation hN p)⁻¹)).injective
  rw [cavitySpectralProjection, LinearIsometryEquiv.apply_symm_apply,
    cavityPermutationSpin_cancel, ← cavity_specialRotation_mul_apply,
    inv_mul_cancel_right]
  simp only [cavitySpectralProjection, LinearIsometryEquiv.apply_symm_apply]

lemma cavitySpectralProjection_permutation_sq {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N) (I : Finset (Fin N))
    (σ : Spin N) (j : Fin N) :
    (cavitySpectralProjection (specialRotation (U * (spectralPermutation hN p)⁻¹)) I
      (spinVector (cavitySignedSpinPermutation p (cavityPermutationFlip hN p) σ)) j) ^ 2 =
    (cavitySpectralProjection (specialRotation U) I (spinVector σ) (p j)) ^ 2 := by
  rw [cavitySpectralProjection_permutation]
  have h := spectralPermutation_coordinate_sq hN p (1 : SpecialOrthogonal N)
    (cavitySpectralProjection (specialRotation U) I (spinVector σ)) j
  simpa only [mul_one, cavity_specialRotation_one] using h

lemma measurable_cavitySpectralProjection_site {N : ℕ}
    (I : Finset (Fin N)) (σ : Spin N) (j : Fin N) :
    Measurable (fun U : SpecialOrthogonal N =>
      cavitySpectralProjection (specialRotation U) I (spinVector σ) j) := by
  simp only [cavitySpectralProjection, cavity_specialRotation_symm, specialRotation_apply]
  apply Finset.measurable_sum
  intro k _
  have hentry : Measurable (fun U : SpecialOrthogonal N =>
      ((U⁻¹ : SpecialOrthogonal N) : Matrix (Fin N) (Fin N) ℝ) j k) := by
    change Measurable (fun U : SpecialOrthogonal N => (U : Matrix (Fin N) (Fin N) ℝ) k j)
    exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp measurable_subtype_coe)
  apply hentry.mul
  by_cases hk : k ∈ I
  · simpa only [hk, ite_true, specialRotation_apply] using
      measurable_specialRotation_eval (spinVector σ) k
  · simp only [hk, ite_false]
    exact measurable_const

end InvariantIsing

end

end OAI
