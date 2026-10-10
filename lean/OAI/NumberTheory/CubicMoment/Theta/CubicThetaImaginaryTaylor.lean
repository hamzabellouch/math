import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! A polynomial remainder bound for a purely imaginary exponential.
The bound has no exponential loss in the frequency. -/
noncomputable section
open Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicTheta_exp_real_iteratedDeriv (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (c*(t:ℂ)))=
      fun t : ℝ => c^n*Complex.exp (c*(t:ℂ)) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [iteratedDeriv_succ,hn]
      funext t
      have he : HasDerivAt (fun u : ℝ => Complex.exp (c*(u:ℂ)))
          (c*Complex.exp (c*(t:ℂ))) t := by
        simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,mul_comm] using
          ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).cexp
      rw [(he.const_mul (c^n)).deriv,pow_succ]
      ring

theorem cubicTheta_exp_imaginary_taylor (c : ℂ) (hc : c.re=0) (n : ℕ)
    {r : ℝ} (hr : 0≤r) :
    ‖Complex.exp (c*(r:ℂ))-
      ∑ j∈Finset.range (n+1), (c*(r:ℂ))^j/(j.factorial:ℂ)‖≤
        ‖c‖^(n+1)*r^(n+1)/(n.factorial:ℝ) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp [Finset.sum_range_succ']
  let f : ℝ→ℂ := fun t => Complex.exp (c*(t:ℂ))
  have hf (k : ℕ) : ContDiff ℝ k f := by
    dsimp [f]
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hi (k : ℕ) (t : ℝ) (ht : t∈Icc 0 r) :
      iteratedDerivWithin k f (Icc 0 r) t=c^k*Complex.exp (c*(t:ℂ)) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hr) (hf k).contDiffAt ht]
    exact congrFun (cubicTheta_exp_real_iteratedDeriv c k) t
  have ht := taylor_mean_remainder_bound hr.le (hf (n+1)).contDiffOn
    (right_mem_Icc.mpr hr.le) (C := ‖c‖^(n+1)) (fun t ht => by
      rw [hi (n+1) t ht,norm_mul,norm_pow,Complex.norm_exp]
      simp [Complex.mul_re,hc])
  have hp : taylorWithinEval f n (Icc 0 r) 0 r=
      ∑ j∈Finset.range (n+1), (c*(r:ℂ))^j/(j.factorial:ℂ) := by
    rw [taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hi j 0 (left_mem_Icc.mpr hr.le)]
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one,sub_zero,
      Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,
      Complex.ofReal_natCast,mul_pow,div_eq_mul_inv]
    ring
  simpa only [hp,sub_zero,f] using ht

end CubicFirstMoment

end

end OAI
