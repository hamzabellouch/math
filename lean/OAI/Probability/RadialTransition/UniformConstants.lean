import OAI.Probability.RadialTransition.ScaleBudgets

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma boxPressureConstant_eq {t β : ℝ} (ht : 0 < t) (hβ : 0 < β) (h A : ℝ) :
    boxPressureConstant t β h A =
      (9216/t^3)*Real.exp (16/15*(1/64)*Real.exp (t*h+β*(t^2/2)))*referenceRowBound t A := by
  unfold boxPressureConstant localMomentBound
  field_simp
  ring

lemma boxPressureConstant_mono {t β γ h j A B : ℝ} (ht : 0 < t) (hβ : 0 < β)
    (hβγ : β ≤ γ) (hhj : h ≤ j) (hA : 0 ≤ A) (hAB : A ≤ B) :
    boxPressureConstant t β h A ≤ boxPressureConstant t γ j B := by
  rw [boxPressureConstant_eq ht hβ, boxPressureConstant_eq ht (hβ.trans_le hβγ)]
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    exact add_le_add (mul_le_mul_of_nonneg_left hhj ht.le)
      (mul_le_mul_of_nonneg_right hβγ (by positivity))
  · unfold referenceRowBound
    gcongr
    exact mul_nonneg (by positivity) (inv_nonneg.mpr bumpIntegral_pos.le)
  · exact referenceRowBound_nonneg ht.le hA
  · positivity

lemma log_volume_error_le {F s t : ℝ} (hF : 0 ≤ F) (hs : 1 ≤ s) (ht : 0 < t) :
    Real.log ((F+2)*s^3)/(t*s^3) ≤ (F+5)/(t*s) := by
  have hs0 : 0 < s := by linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < F+2 by linarith)
  have h2 := Real.log_le_sub_one_of_pos hs0
  have hs2 : 1 ≤ s^2 := one_le_pow₀ hs
  have hss : s ≤ s^2 := by nlinarith
  have hnum : Real.log (F+2)+3*Real.log s ≤ (F+5)*s^2 := by
    nlinarith [mul_le_mul_of_nonneg_left hs2 hF]
  apply (div_le_iff₀ (by positivity : 0 < t*s^3)).mpr
  calc
    _ ≤ (F+5)*s^2 := by simpa using hnum
    _ = _ := by field_simp [ht.ne', hs0.ne']

lemma kernelUpperError_le_row {q : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    kernelUpperError q R ≤ kernelRowError q R := by
  unfold kernelUpperError kernelRowError
  apply div_le_div_of_nonneg_right _ hR
  have hh := mul_nonneg (inv_nonneg.mpr bumpIntegral_pos.le) (Nat.cast_nonneg (α := ℝ) q)
  nlinarith

lemma kernelUpperError_nonneg (q : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ kernelUpperError q R := by unfold kernelUpperError; positivity

end RadialTransition
end

end OAI
