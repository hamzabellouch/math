import OAI.NumberTheory.TotientAsymptotic.FordDimensionScale
import OAI.NumberTheory.TotientAsymptotic.QuarterPowerBudget

namespace OAI

/-! The explicit preliminary counting errors fit the Gaussian Ford scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma logarithmic_gaussian_budget {b t c : ℝ} (hb : 1 ≤ b) (ht : 0 ≤ t)
    (hexp : Real.exp ((3/5:ℝ)*t) ≤ b)
    (hbudget : 100*(Real.log (b+4)+30)^2 ≤ c*b) :
    (b+4)^6*Real.exp (9*(Real.log (b+4))^2-c*b) ≤ Real.exp (-t^2/4) := by
  have hb0 : 0 < b := by linarith
  have hlog : 0 ≤ Real.log (b+4) := Real.log_nonneg (by linarith)
  have hlower : (3/5:ℝ)*t ≤ Real.log b := by
    have hh := Real.log_le_log (Real.exp_pos _) hexp
    simpa only [Real.log_exp] using hh
  have hmono : Real.log b ≤ Real.log (b+4) := Real.log_le_log hb0 (by linarith)
  have ht' : t ≤ 2*Real.log (b+4) := by linarith only [hlower,hmono,hlog]
  have hsq : t^2/4 ≤ (Real.log (b+4))^2 := by
    nlinarith only [sq_nonneg (2*Real.log (b+4)-t),mul_nonneg ht (sub_nonneg.mpr ht')]
  have hpow : (b+4)^6=Real.exp (6*Real.log (b+4)) := by
    simpa only [Nat.cast_ofNat,Real.exp_log (by linarith : 0 < b+4)] using
      (Real.exp_nat_mul (Real.log (b+4)) 6).symm
  rw [hpow,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hbudget,hsq,hlog,sq_nonneg (Real.log (b+4))]

lemma bootstrap_error_gaussian_budget {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      (B x+4)^6*Real.exp (9*(Real.log (B x+4))^2-c*B x) ≤
        Real.exp (-(m x:ℝ)^2/4) := by
  filter_upwards [dimension_exponential_lower,
    B_tendsto.eventually (eventually_ge_atTop (max 1 (((10000*(0+31)^2)/c)^(4/3:ℝ))))]
    with x hexp hb
  have hb1 : 1 ≤ B x := (le_max_left _ _).trans hb
  have hthreshold : ((10000*((0:ℝ)+31)^2)/c)^(4/3:ℝ) ≤ B x := (le_max_right _ _).trans hb
  have hbudget := four_thirds_threshold_budget hb1 (le_refl (0:ℝ)) hc hthreshold
  exact logarithmic_gaussian_budget hb1 (Nat.cast_nonneg _) hexp
    (by simpa only [add_zero] using hbudget)

end TotientAsymptotic

end

end OAI
