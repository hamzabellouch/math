import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerron
import OAI.NumberTheory.JointDickman.Analysis.SquarefreePerronBounds
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeContourIdentification
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszKernel

namespace OAI

/-! # Normalized Perron inversion for the actual squarefree coefficients -/
namespace JointDickman
open Complex MeasureTheory

theorem squarefreeNormalizedPerron_eq (z L : ℝ) (w : ℂ) :
    (Real.exp L:ℂ)*squarefreeNormalizedPerron z L w =
      LSeries (fun n => (squarefreeWeight z n:ℂ)) (1+w) * Perron.f (Real.exp L) (1+w) := by
  have he : ((Real.exp L:ℝ):ℂ)^(1+w) = (Real.exp L:ℂ)*exp ((L:ℂ)*w) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'),
      ←Complex.ofReal_log (Real.exp_pos L).le,Real.log_exp,mul_add,mul_one,Complex.exp_add,
      ←Complex.ofReal_exp]
  rw [squarefreeNormalizedPerron,Perron.f,he]
  have hden : (1:ℂ)+w+1 = 2+w := by ring
  rw [hden]
  ring

theorem squarefreeNormalizedPerron_riesz {z L c : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hc : 0 < c) (hxnat : ∀ n : ℕ, Real.exp L ≠ (n:ℝ)) :
    (Real.exp L:ℂ)*VerticalIntegral' (squarefreeNormalizedPerron z L) c =
      squarefreeRieszSum z (Real.exp L) := by
  have hp := squarefree_perron_riesz hz hz1 (Real.exp_pos L)
    (show 1 < 1+c by linarith) hxnat
  rw [←hp]
  simp only [VerticalIntegral',VerticalIntegral,smul_eq_mul]
  have heq : (fun t : ℝ => (Real.exp L:ℂ)*squarefreeNormalizedPerron z L ((c:ℂ)+(t:ℂ)*I)) =
      (fun t : ℝ => LSeries (fun n => (squarefreeWeight z n:ℂ)) (((1+c:ℝ):ℂ)+(t:ℂ)*I) *
        Perron.f (Real.exp L) (((1+c:ℝ):ℂ)+(t:ℂ)*I)) := by
    funext t
    rw [squarefreeNormalizedPerron_eq]
    congr 2 <;> push_cast <;> ring
  rw [←heq,integral_const_mul]
  ring

theorem squarefreeNormalizedPerron_eq_continuation {z L δ T : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hδ : 0 < δ) (hT : 0 < T)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (zetaOpenRectangle δ T)) (hf1 : f 1 = 0)
    (he : ∀ s ∈ zetaOpenRectangle δ T, exp (f s) = zetaPoleFactor s)
    {w : ℂ} (hw : 1+w ∈ zetaOpenRectangle 0 T) :
    squarefreeNormalizedPerron z L w =
      fractionalContourIntegrand z (squarefreeRieszKernel z L f) w := by
  rw [squarefreeRieszKernel_factorization,
    squarefreeContourSeries_eq_LSeries_on_right hz hz1 hδ hT hf hf1 he (1+w) hw]
  rfl

end JointDickman

end OAI
