import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszKernel
import OAI.NumberTheory.JointDickman.Analysis.RieszDenominatorBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace OAI

/-! # Integrable majorants for the squarefree Riesz contour -/
namespace JointDickman
open Complex Set MeasureTheory

theorem squarefreeRieszKernel_bound {z L C B : ℝ} (hz : 0 ≤ z)
    {f : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0) (hs : 1/2 ≤ (1+w).re)
    (hf : exp (f (1+w)) = zetaPoleFactor (1+w))
    (hG : ‖squarefreeAnalyticFactor z (1+w)‖ ≤ C)
    (hζ : ‖riemannZeta (1+w)‖ ≤ B) :
    ‖fractionalContourIntegrand z (squarefreeRieszKernel z L f) w‖ ≤
      5*C*B^z*Real.exp (L*w.re)/(1+w.im^2) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hG
  have hB : 0 ≤ B := (norm_nonneg _).trans hζ
  have hden : 1/(‖1+w‖*‖2+w‖) ≤ 5/(1+w.im^2) := by
    simpa only [show (1:ℂ)+w+1 = 2+w by ring,add_im,one_im,zero_add] using
      rieszDenominator_inv_bound hs
  rw [squarefreeRieszKernel_norm hw hf,div_eq_mul_inv]
  calc
    _ ≤ (C*B^z*Real.exp (L*w.re))*(5/(1+w.im^2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul hG (Real.rpow_le_rpow (norm_nonneg _) hζ hz)
            (Real.rpow_nonneg (norm_nonneg _) _) hC) (Real.exp_pos _).le
      · simpa only [one_div] using hden
      · positivity
      · positivity
    _ = _ := by ring

theorem verticalIntegral_bound_by_cauchy {f : ℂ → ℂ} {σ T D : ℝ}
    (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hf : ∀ t ∈ Ioc (-T) T, ‖f ((σ:ℂ)+(t:ℂ)*I)‖ ≤ D/(1+t^2)) :
    ‖VIntegral f σ (-T) T‖ ≤ D*Real.pi := by
  have hi : Integrable (fun t : ℝ => D/(1+t^2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul D
  rw [VIntegral,norm_smul,Complex.norm_I,one_mul,
    intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  calc
    _ ≤ ∫ t : ℝ in Ioc (-T) T, D/(1+t^2) := by
      apply norm_integral_le_of_norm_le hi.restrict
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hf t ht
    _ ≤ ∫ t : ℝ, D/(1+t^2) := by
      apply setIntegral_le_integral hi
      filter_upwards with t
      positivity
    _ = D*Real.pi := by
      simp only [div_eq_mul_inv,integral_const_mul,integral_univ_inv_one_add_sq]

end JointDickman

end OAI
