import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeEulerAtOne
import OAI.NumberTheory.JointDickman.Analysis.ZetaPoleFactor
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace OAI

/-! # The analytic factor determining the Selberg–Delange coefficients -/
namespace JointDickman

/-- Removing the principal power singularity of `ζ(s)^z` and the Perron denominator. -/
noncomputable def squarefreeSingularFactor (z : ℝ) (s : ℂ) : ℂ :=
  squarefreeAnalyticFactor z s * Complex.exp ((z:ℂ)*Complex.log (zetaPoleFactor s)) / s

 theorem squarefreeSingularFactor_analyticAt_one {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    AnalyticAt ℂ (squarefreeSingularFactor z) 1 := by
  have hG := squarefreeAnalyticFactor_analyticOnNhd hz hz1 (1:ℂ) (by norm_num)
  have hH : AnalyticAt ℂ (fun s => Complex.log (zetaPoleFactor s)) 1 :=
    zetaPoleFactor_analyticAt_one.clog (by simp only [zetaPoleFactor_one]; exact Complex.one_mem_slitPlane)
  exact (hG.mul ((analyticAt_const.mul hH).cexp')).div analyticAt_id (by norm_num)

 theorem squarefreeSingularFactor_one {z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) :
    squarefreeSingularFactor z 1 = (squarefreeLeadingConstant z * Real.Gamma z : ℝ) := by
  simpa only [squarefreeSingularFactor,zetaPoleFactor_one,Complex.log_one,mul_zero,Complex.exp_zero,
    mul_one,div_one] using squarefreeAnalyticFactor_one_gamma hz hz1

 theorem squarefreeSingularFactor_hasPowerSeries {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesAt (squarefreeSingularFactor z) p 1 :=
  squarefreeSingularFactor_analyticAt_one hz hz1

end JointDickman

end OAI
