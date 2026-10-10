import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! # A bounded inverse for a coordinate matrix close to the identity -/

namespace DefocusingNLS

theorem exists_nearIdentity_inverse {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : F →L[ℝ] F) (hA : ‖A - ContinuousLinearMap.id ℝ F‖ < 1 / 2) :
    ∃ D : F →L[ℝ] F, D.comp A = ContinuousLinearMap.id ℝ F ∧
      A.comp D = ContinuousLinearMap.id ℝ F ∧ ‖D‖ ≤ 2 := by
  have hsmall : ‖(1 : F →L[ℝ] F) - A‖ < 1 := by
    rw [norm_sub_rev]
    exact hA.trans (by norm_num)
  let U := Units.oneSub ((1 : F →L[ℝ] F) - A) hsmall
  have hU : (U : F →L[ℝ] F) = A := by
    simp only [U, Units.val_oneSub, sub_sub_cancel]
  let D : F →L[ℝ] F := ↑U⁻¹
  have hDA : D.comp A = ContinuousLinearMap.id ℝ F := by
    change U.inv * A = 1
    rw [← hU]
    exact U.inv_val
  have hAD : A.comp D = ContinuousLinearMap.id ℝ F := by
    change A * U.inv = 1
    rw [← hU]
    exact U.val_inv
  refine ⟨D, hDA, hAD, ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v => ?_)⟩
  have he : A (D v) = v := congrArg (fun T : F →L[ℝ] F => T v) hAD
  have hd : ((1 : F →L[ℝ] F) - A) (D v) = D v - v := by
    simp only [sub_apply, one_apply_eq_self, he]
  have hb := ((1 : F →L[ℝ] F) - A).le_opNorm (D v)
  rw [hd] at hb
  have hnorm : ‖(1 : F →L[ℝ] F) - A‖ = ‖A - ContinuousLinearMap.id ℝ F‖ :=
    norm_sub_rev _ _
  rw [hnorm] at hb
  have hmul := mul_le_mul_of_nonneg_right hA.le (norm_nonneg (D v))
  have ht := norm_add_le (D v - v) v
  rw [sub_add_cancel] at ht
  linarith

end DefocusingNLS

end OAI
