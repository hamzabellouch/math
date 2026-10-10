import Mathlib.Tactic.Positivity
import OAI.NumberTheory.Ostmann.Arithmetic.ScaleBudget

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted
open ScaleBudget Filter

theorem eventually_weighted_modulus_error :
    ∀ᶠ L : ℝ in atTop, ∀ M : ℕ, 0 < M →
      Real.log (M:ℝ) ≤ Real.exp (giant.μ*L) →
      (M:ℝ)*Real.exp (-Real.exp (giant.target*L)) ≤
        Real.exp (-Real.exp ((1/80:ℝ)*L)) := by
  filter_upwards [eventually_double_exp_error 1 0
    (a:=giant.μ) (b:=giant.target) (d:=1/80) (c:=1)
    (by norm_num [giant]) (by norm_num [giant]) (by norm_num)] with L hL
  intro M hM hmod
  have hm : (0:ℝ) < M := by exact_mod_cast hM
  calc
    _ = Real.exp (Real.log (M:ℝ)-Real.exp (giant.target*L)) := by
      rw [Real.exp_sub,Real.exp_log hm,div_eq_mul_inv,Real.exp_neg]
    _ ≤ Real.exp (-Real.exp (giant.target*L)+Real.exp (giant.μ*L)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := by simpa only [pow_zero,mul_one,one_mul,neg_mul] using hL

end Ostmann.Arithmetic.HistoryGiantXiReplacementWeighted

end

end OAI
