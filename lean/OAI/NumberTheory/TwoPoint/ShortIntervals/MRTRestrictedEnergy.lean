import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTPrimeProducts

namespace OAI

/-! Finite energy bounds on arbitrary measurable frequency classes.
They retain the explicit coarse-bin count and permit the coefficient
bounds to vary from bin to bin. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_continuous_square_integrable {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    IntegrableOn (fun t => ‖F t‖ ^ 2) E := by
  have hi : IntegrableOn (fun t => ‖F t‖ ^ 2) (Set.Ioc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      ((hF.norm.pow 2).intervalIntegrable _ _)
  exact hi.mono_set hE

lemma mrt_restricted_square_le_interval {F : ℝ → ℂ} (hF : Continuous F)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖F t‖ ^ 2) ≤ ∫ t in -T..T, ‖F t‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  exact setIntegral_mono_set
    (mrt_continuous_square_integrable hF hT (Set.Subset.refl _))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall hE)

/-- Frequency-restricted Cauchy--Schwarz, with the actual pointwise
short-prime bounds and the cofactor energies left explicit. -/
theorem mrt_restricted_product_sum_energy {ι : Type*} (J : Finset ι)
    (Q R : ι → ℝ → ℂ) (hR : ∀ j ∈ J, Continuous (R j))
    (A : ι → ℝ)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T)
    (hQ : ∀ j ∈ J, ∀ t ∈ E, ‖Q j t‖ ≤ A j) :
    (∫ t in E, ‖∑ j ∈ J, Q j t * R j t‖ ^ 2) ≤
      (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 *
        (∫ t in -T..T, ‖R j t‖ ^ 2) := by
  have hi (j : ι) (hj : j ∈ J) := mrt_continuous_square_integrable (hR j hj) hT hE
  calc
    _ ≤ ∫ t in E, (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * ‖R j t‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((integrable_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))).const_mul _)
      intro t ht
      apply (mrt_norm_sum_sq_le_card J (fun j => Q j t * R j t)).trans
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hQ j hj t ht) 2) (sq_nonneg _)
    _ = (J.card : ℝ) * ∑ j ∈ J, (A j) ^ 2 * (∫ t in E, ‖R j t‖ ^ 2) := by
      rw [integral_const_mul, integral_finsetSum J (fun j hj => (hi j hj).const_mul ((A j) ^ 2))]
      simp only [integral_const_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (mrt_restricted_square_le_interval (hR j hj) hT hE) (sq_nonneg _)

/-- Split a polynomial into a coarse approximation and its actual error
on a frequency class, bounding only the error by its full-interval energy. -/
theorem mrt_restricted_energy_split (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G)
    {T : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : E ⊆ Set.Ioc (-T) T) :
    (∫ t in E, ‖F t‖ ^ 2) ≤
      2 * (∫ t in -T..T, ‖F t - G t‖ ^ 2) + 2 * (∫ t in E, ‖G t‖ ^ 2) := by
  have hiG := mrt_continuous_square_integrable hG hT hE
  have hiD : IntegrableOn (fun t => ‖F t - G t‖ ^ 2) E :=
    mrt_continuous_square_integrable (hF.sub hG) hT hE
  calc
    _ ≤ ∫ t in E, (2 * ‖F t - G t‖ ^ 2 + 2 * ‖G t‖ ^ 2) := by
      apply setIntegral_mono_of_nonneg (fun _ _ => sq_nonneg _) _
        ((hiD.const_mul 2).add (hiG.const_mul 2))
      intro t _
      change ‖F t‖ ^ 2 ≤ 2 * ‖F t - G t‖ ^ 2 + 2 * ‖G t‖ ^ 2
      have ht := norm_add_le (F t - G t) (G t)
      rw [sub_add_cancel] at ht
      nlinarith [sq_nonneg (‖F t - G t‖ - ‖G t‖), norm_nonneg (F t),
        norm_nonneg (F t - G t), norm_nonneg (G t)]
    _ = 2 * (∫ t in E, ‖F t - G t‖ ^ 2) + 2 * (∫ t in E, ‖G t‖ ^ 2) := by
      rw [integral_add (hiD.const_mul 2) (hiG.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (mrt_restricted_square_le_interval (hF.sub hG) hT hE) (by norm_num)) le_rfl

end TwoPointCorrelations

end OAI
