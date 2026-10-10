import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

namespace OAI

/-! # Squared-distance descent toward a negative ray

Positive character certificates will point against the residual vector. A
large enough residual then decreases by at least one squared-distance unit.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped InnerProductSpace
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def negativeRayCoefficient (t q : E) : ℝ := min 0 ⟪q, t⟫_ℝ / ‖t‖ ^ 2

def negativeRayResidual (t q : E) : E := q - negativeRayCoefficient t q • t

theorem negativeRayCoefficient_nonpos (t q : E) : negativeRayCoefficient t q ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (min_le_left _ _) (sq_nonneg _)

theorem negativeRayResidual_inner_nonneg (t q : E) :
    0 ≤ ⟪negativeRayResidual t q, t⟫_ℝ := by
  by_cases ht : t = 0
  · subst t
    simp
  have hk : 0 < ‖t‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ht)
  rw [negativeRayResidual, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, negativeRayCoefficient, div_mul_cancel₀ _ (ne_of_gt hk)]
  exact sub_nonneg.mpr (min_le_right _ _)

theorem negativeRayResidual_minimizes (t q : E) (c : ℝ) (hc : c ≤ 0) :
    ‖negativeRayResidual t q‖ ^ 2 ≤ ‖q - c • t‖ ^ 2 := by
  by_cases ht : t = 0
  · subst t
    simp [negativeRayResidual]
  have hk : 0 < ‖t‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ht)
  by_cases ha : ⟪q, t⟫_ℝ ≤ 0
  · have horth : ⟪negativeRayResidual t q, t⟫_ℝ = 0 := by
      rw [negativeRayResidual, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, negativeRayCoefficient, min_eq_right ha,
        div_mul_cancel₀ _ (ne_of_gt hk), sub_self]
    have he : q - c • t = negativeRayResidual t q +
        (negativeRayCoefficient t q - c) • t := by
      unfold negativeRayResidual
      module
    rw [he, norm_add_sq_real, real_inner_smul_right, horth]
    nlinarith [sq_nonneg ‖(negativeRayCoefficient t q - c) • t‖]
  · have ha' : 0 ≤ ⟪q, t⟫_ℝ := le_of_lt (lt_of_not_ge ha)
    have hz : negativeRayCoefficient t q = 0 := by
      rw [negativeRayCoefficient, min_eq_left ha', zero_div]
    rw [negativeRayResidual, hz, zero_smul, sub_zero, norm_sub_sq_real,
      real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hca : c * ⟪q, t⟫_ℝ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc ha'
    nlinarith [sq_nonneg c]

theorem norm_sq_drop_of_inward_pairing (v w : E) (hv : v ≠ 0)
    (δ : ℝ) (hdir : δ ≤ -⟪‖v‖⁻¹ • v, w⟫_ℝ)
    (hlarge : ‖w‖ ^ 2 + 1 ≤ 2 * δ * ‖v‖) :
    ‖v + w‖ ^ 2 + 1 ≤ ‖v‖ ^ 2 := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [real_inner_smul_left] at hdir
  have hm := mul_le_mul_of_nonneg_right hdir (norm_nonneg v)
  have he : -(‖v‖⁻¹ * ⟪v, w⟫_ℝ) * ‖v‖ = -⟪v, w⟫_ℝ := by field_simp
  rw [he] at hm
  rw [norm_add_sq_real]
  linarith

theorem negativeRayResidual_sq_drop (t q w : E)
    (hv : negativeRayResidual t q ≠ 0) (δ : ℝ)
    (hdir : δ ≤ -⟪‖negativeRayResidual t q‖⁻¹ • negativeRayResidual t q, w⟫_ℝ)
    (hlarge : ‖w‖ ^ 2 + 1 ≤ 2 * δ * ‖negativeRayResidual t q‖) :
    ‖negativeRayResidual t (q + w)‖ ^ 2 + 1 ≤ ‖negativeRayResidual t q‖ ^ 2 := by
  have hmin := negativeRayResidual_minimizes t (q + w) (negativeRayCoefficient t q)
    (negativeRayCoefficient_nonpos t q)
  have he : q + w - negativeRayCoefficient t q • t = negativeRayResidual t q + w := by
    unfold negativeRayResidual
    abel
  rw [he] at hmin
  have hdrop := norm_sq_drop_of_inward_pairing _ _ hv δ hdir hlarge
  linarith

theorem negativeRayResidual_ceil_drop (t q w : E)
    (hv : negativeRayResidual t q ≠ 0) (δ : ℝ)
    (hdir : δ ≤ -⟪‖negativeRayResidual t q‖⁻¹ • negativeRayResidual t q, w⟫_ℝ)
    (hlarge : ‖w‖ ^ 2 + 1 ≤ 2 * δ * ‖negativeRayResidual t q‖) :
    ⌈‖negativeRayResidual t (q + w)‖ ^ 2⌉₊ < ⌈‖negativeRayResidual t q‖ ^ 2⌉₊ := by
  have h := Nat.ceil_mono (negativeRayResidual_sq_drop t q w hv δ hdir hlarge)
  rw [Nat.ceil_add_one (sq_nonneg _)] at h
  exact lt_of_lt_of_le (Nat.lt_succ_self _) h

end PolycyclicRecognition

end

end OAI
