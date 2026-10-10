import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightScaleNumerics
import OAI.NumberTheory.Ostmann.Construction.GiantWindowScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction.SourceFrequencyBounds
open Filter
open Conclusion

theorem frequency_lt_of_log_lower_eventually (Bs BD Bz : ℝ) {k : ℕ} (hk : 0<k)
    {a : ℝ} (ha : 0<a) :
    ∀ᶠ L : ℝ in atTop, ∀ j : ℕ, j≤k → ∀ p : ℕ, 0<p →
      Real.exp (a*L)≤Real.log (p:ℝ) → frequencyBound Bs BD Bz k L j<p := by
  let C := scaleLinearConstant Bs BD Bz k
  have hC : 0<C := scaleLinearConstant_pos Bs BD Bz k
  have hrate : ∀ᶠ L : ℝ in atTop, C*bulkScale k+1≤Real.exp (a*L)/L := by
    simpa only [Real.rpow_one] using
      (tendsto_exp_mul_div_rpow_atTop 1 a ha).eventually_ge_atTop (C*bulkScale k+1)
  filter_upwards [hrate,(bulkSize_tendsto_atTop hk).eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℝ)] with L hr hm hL
  intro j hj p hp hlog
  have hLpos : 0<L := by linarith
  have hm' : 1≤bulkSize k L := by exact_mod_cast hm
  have hbudget := frequencyBudget_le_linear Bs BD Bz k L hm' hj
  have hupper := (bulkSize_bounds k hLpos.le).2
  have hmult := mul_le_mul_of_nonneg_left hupper hC.le
  have hrate' := (le_div_iff₀ hLpos).mp hr
  have hb : frequencyBudget Bs BD Bz k L j<Real.log (p:ℝ) := by
    change frequencyBudget Bs BD Bz k L j≤C*(bulkSize k L:ℝ) at hbudget
    nlinarith
  have hp' : (0:ℝ)<p := by exact_mod_cast hp
  have hexp : Real.exp (frequencyBudget Bs BD Bz k L j)<(p:ℝ) := by
    simpa only [Real.exp_log hp'] using Real.exp_lt_exp.mpr hb
  have hfloor : (frequencyBound Bs BD Bz k L j:ℝ)≤
      Real.exp (frequencyBudget Bs BD Bz k L j) := Nat.floor_le (Real.exp_pos _).le
  exact_mod_cast hfloor.trans_lt hexp

end Ostmann.Construction.SourceFrequencyBounds

end

end OAI
