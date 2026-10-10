import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerBound
import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeSingularFactor

namespace OAI

/-! # Continuation of the squarefree series on a slit zero-free rectangle -/
namespace JointDickman
open Set Filter
open scoped Topology

noncomputable def squarefreeContourSeries (z : ℝ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  squarefreeAnalyticFactor z s * Complex.exp ((z:ℂ)*(f s-Complex.log (s-1)))

theorem squarefreeContourSeries_analyticAt {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    {f : ℂ → ℂ} {s : ℂ} (hf : AnalyticAt ℂ f s) (hs : 1/2 < s.re)
    (hslit : s-1 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (squarefreeContourSeries z f) s := by
  have hl := (analyticAt_id.sub analyticAt_const).clog hslit
  exact (squarefreeAnalyticFactor_analyticOnNhd hz hz1 s hs).mul
    ((analyticAt_const.mul (hf.sub hl)).cexp')

theorem squarefreeContourSeries_norm {z : ℝ} {f : ℂ → ℂ} {s : ℂ}
    (hs : s ≠ 1) (hf : Complex.exp (f s) = zetaPoleFactor s) :
    ‖squarefreeContourSeries z f s‖ = ‖squarefreeAnalyticFactor z s‖*‖riemannZeta s‖^z := by
  have he : Complex.exp (f s-Complex.log (s-1)) = riemannZeta s := by
    rw [Complex.exp_sub,hf,Complex.exp_log (sub_ne_zero.mpr hs),zetaPoleFactor_eq hs]
    exact mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs)
  rw [squarefreeContourSeries,norm_mul,norm_exp_real_mul_of_exp_eq z he]

theorem squarefreeContourSeries_local {z : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousAt f 1) (h0 : f 1 = 0)
    (he : (fun s => Complex.exp (f s)) =ᶠ[𝓝 1] zetaPoleFactor) :
    (fun s => squarefreeContourSeries z f s / s) =ᶠ[𝓝 1]
      (fun s => squarefreeSingularFactor z s * Complex.exp (-(z:ℂ)*Complex.log (s-1))) := by
  filter_upwards [normalized_log_eq_principal_near hf h0 he] with s hs
  simp only [squarefreeContourSeries,hs,squarefreeSingularFactor,mul_sub,Complex.exp_sub,
    Complex.exp_neg,neg_mul]
  ring

end JointDickman

end OAI
