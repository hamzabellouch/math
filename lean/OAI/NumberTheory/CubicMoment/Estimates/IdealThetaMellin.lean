import OAI.NumberTheory.CubicMoment.Estimates.IdealThetaDecay
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

namespace OAI

/-! Exact Mellin transform of the complete ideal theta series. -/
noncomputable section
namespace CubicFirstMoment

lemma idealTheta_one_mellin (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    mellin (idealTheta 1 χ) s =
      Complex.Gamma s * normDirichletSeries χ idealExponentNorm s := by
  have hsum : Summable (fun ν => ‖χ ν‖ / idealExponentNorm ν^s.re) := by
    simpa only [Real.rpow_neg (idealExponentNorm_pos _).le,div_eq_mul_inv] using
      summable_ideal_character_weight hs χ hχ
  have h := hasSum_mellin (fun ν => Or.inr (idealExponentNorm_pos ν))
    (show 0 < s.re by linarith) (F := idealTheta 1 χ) (fun t ht => by
      simpa only [idealTheta,div_one] using (idealTheta_summable zero_lt_one ht χ hχ).hasSum) hsum
  rw [← h.tsum_eq]
  simp only [normDirichletSeries,Complex.cpow_neg,div_eq_mul_inv,mul_assoc]
  exact tsum_mul_left

lemma idealTheta_scale (A : ℝ)
    (χ : EisensteinIdealExponent → ℂ) :
    idealTheta A χ = fun t => idealTheta 1 χ (t*(1/A)) := by
  funext t
  unfold idealTheta
  apply tsum_congr
  intro ν
  apply congrArg (fun u : ℝ => χ ν*(Real.exp u : ℝ))
  ring

lemma idealTheta_mellin {A : ℝ} (hA : 0 < A)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (idealTheta A χ) s =
      (A:ℂ)^s * Complex.Gamma s * normDirichletSeries χ idealExponentNorm s := by
  rw [idealTheta_scale A χ,mellin_comp_mul_right _ _ (one_div_pos.mpr hA),
    idealTheta_one_mellin χ hχ hs]
  have hp : ((1/A:ℝ):ℂ)^(-s) = (A:ℂ)^s := by
    simpa using mellin_scale_cpow zero_lt_one hA s
  rw [hp,smul_eq_mul,mul_assoc]

end CubicFirstMoment

end

end OAI
