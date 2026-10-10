import Mathlib.Analysis.InnerProductSpace.LaxMilgram

namespace OAI

/-! The coercive inverse and pressure-energy estimate used in the constrained limit. -/

open InnerProductSpace
namespace DefocusingNLS

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable def spectralPenaltyForm (V : E →L[ℝ] H) (P : H →L[ℝ] H) (a : ℝ) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  innerSL ℝ + a⁻¹ • (innerSL ℝ).bilinearComp (P.comp V) V

theorem spectralPenaltyForm_apply (V : E →L[ℝ] H) (P : H →L[ℝ] H) (a : ℝ) (u v : E) :
    spectralPenaltyForm V P a u v=inner ℝ u v+a⁻¹*inner ℝ (P (V u)) (V v) := rfl

theorem spectralPenaltyForm_coercive (V : E →L[ℝ] H) (P : H →L[ℝ] H)
    (a : ℝ) (ha : 0 < a) (hP : ∀ x, 0 ≤ inner ℝ (P x) x) :
    IsCoercive (spectralPenaltyForm V P a) := by
  refine ⟨1,zero_lt_one,fun u => ?_⟩
  rw [spectralPenaltyForm_apply,real_inner_self_eq_norm_sq]
  have hp : 0 ≤ a⁻¹*inner ℝ (P (V u)) (V u) := mul_nonneg (inv_nonneg.mpr ha.le) (hP _)
  nlinarith

variable [CompleteSpace E]

noncomputable def spectralPenaltyInverse (V : E →L[ℝ] H) (P : H →L[ℝ] H)
    (a : ℝ) (ha : 0 < a) (hP : ∀ x, 0 ≤ inner ℝ (P x) x) :
    StrongDual ℝ E →L[ℝ] E :=
  (spectralPenaltyForm_coercive V P a ha hP).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem spectralPenaltyInverse_equation (V : E →L[ℝ] H) (P : H →L[ℝ] H)
    (a : ℝ) (ha : 0 < a) (hP : ∀ x, 0 ≤ inner ℝ (P x) x)
    (F : StrongDual ℝ E) (v : E) :
    spectralPenaltyForm V P a (spectralPenaltyInverse V P a ha hP F) v=F v := by
  have he := (spectralPenaltyForm_coercive V P a ha hP).continuousLinearEquivOfBilin_apply
    (spectralPenaltyInverse V P a ha hP F) v
  change inner ℝ ((spectralPenaltyForm_coercive V P a ha hP).continuousLinearEquivOfBilin
    ((spectralPenaltyForm_coercive V P a ha hP).continuousLinearEquivOfBilin.symm
      ((toDual ℝ E).symm F))) v = _ at he
  rw [ContinuousLinearEquiv.apply_symm_apply,toDual_symm_apply] at he
  exact he.symm

theorem spectralPenaltyInverse_norm (V : E →L[ℝ] H) (P : H →L[ℝ] H)
    (a : ℝ) (ha : 0 < a) (hP : ∀ x, 0 ≤ inner ℝ (P x) x)
    (F : StrongDual ℝ E) : ‖spectralPenaltyInverse V P a ha hP F‖ ≤ ‖F‖ := by
  let u := spectralPenaltyInverse V P a ha hP F
  have he := spectralPenaltyInverse_equation V P a ha hP F u
  rw [spectralPenaltyForm_apply,real_inner_self_eq_norm_sq] at he
  have hp := mul_nonneg (inv_nonneg.mpr ha.le) (hP (V u))
  have hf : F u ≤ ‖F‖*‖u‖ := (le_abs_self _).trans (F.le_opNorm u)
  by_cases hu : ‖u‖=0
  · simpa only [u,hu] using norm_nonneg F
  · have hu0 := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    dsimp only [u] at *
    nlinarith

theorem spectralPenaltyInverse_energy (V : E →L[ℝ] H) (P : H →L[ℝ] H)
    (a : ℝ) (ha : 0 < a) (hP : ∀ x, 0 ≤ inner ℝ (P x) x)
    (F : StrongDual ℝ E) :
    inner ℝ (P (V (spectralPenaltyInverse V P a ha hP F)))
      (V (spectralPenaltyInverse V P a ha hP F)) ≤ a*‖F‖^2 := by
  let u := spectralPenaltyInverse V P a ha hP F
  have he := spectralPenaltyInverse_equation V P a ha hP F u
  rw [spectralPenaltyForm_apply,real_inner_self_eq_norm_sq] at he
  have hn := spectralPenaltyInverse_norm V P a ha hP F
  have hf : F u ≤ ‖F‖*‖u‖ := (le_abs_self _).trans (F.le_opNorm u)
  calc
    inner ℝ (P (V u)) (V u) = a*(a⁻¹*inner ℝ (P (V u)) (V u)) := by
      rw [← mul_assoc,mul_inv_cancel₀ ha.ne',one_mul]
    _ ≤ a*(F u) := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖u‖]) ha.le
    _ ≤ a*(‖F‖*‖u‖) := mul_le_mul_of_nonneg_left hf ha.le
    _ ≤ a*‖F‖^2 := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [pow_two] using mul_le_mul_of_nonneg_left hn (norm_nonneg F)) ha.le

end DefocusingNLS

end OAI
