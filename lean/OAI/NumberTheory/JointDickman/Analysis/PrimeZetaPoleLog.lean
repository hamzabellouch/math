import OAI.NumberTheory.JointDickman.Analysis.PrimeZetaLogAnalytic
import OAI.NumberTheory.JointDickman.Analysis.PrimeZetaLogReal
import OAI.NumberTheory.JointDickman.Analysis.ZetaPoleFactor
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace OAI

/-! # The Euler logarithm of the pole-removed zeta function -/
namespace JointDickman

noncomputable def primeZetaPoleLog (s : ℂ) : ℂ := primeZetaLog s+Complex.log (s-1)

theorem primeZetaPoleLog_exp {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (primeZetaPoleLog s) = zetaPoleFactor s := by
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  rw [primeZetaPoleLog,Complex.exp_add,primeZetaLog_exp hs,
    Complex.exp_log (sub_ne_zero.mpr hs1),zetaPoleFactor_eq hs1,mul_comm]

theorem primeZetaPoleLog_analyticAt {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ primeZetaPoleLog s := by
  have hl : s-1 ∈ Complex.slitPlane := by
    left
    simpa only [Complex.sub_re,Complex.one_re,sub_pos] using hs
  exact (primeZetaLog_analyticOnNhd s hs).add ((analyticAt_id.sub analyticAt_const).clog hl)

theorem primeZetaPoleLog_real {σ : ℝ} (hσ : 1 < σ) :
    primeZetaPoleLog (σ:ℂ) = Complex.log (zetaPoleFactor (σ:ℂ)) := by
  have him : (primeZetaPoleLog (σ:ℂ)).im = 0 := by
    rw [primeZetaPoleLog,Complex.add_im,primeZetaLog_im_eq_zero hσ]
    have hh : (σ:ℂ)-1 = ((σ-1:ℝ):ℂ) := by push_cast; rfl
    rw [hh,←Complex.ofReal_log (by linarith : 0 ≤ σ-1),Complex.ofReal_im,add_zero]
  rw [←primeZetaPoleLog_exp (by simpa only [Complex.ofReal_re] using hσ)]
  symm
  apply Complex.log_exp <;> rw [him] <;> linarith [Real.pi_pos]

end JointDickman

end OAI
