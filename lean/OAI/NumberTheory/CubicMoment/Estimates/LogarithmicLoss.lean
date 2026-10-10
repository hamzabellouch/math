import OAI.NumberTheory.CubicMoment.Estimates.LargeValueExtraction

namespace OAI

/-! The explicit loss in logarithmic pigeonholing has exponent zero. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

theorem HasPowerExponent.logarithm {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop) :
    HasPowerExponent Y (fun j => Real.log (Y j)) 0 := by
  simpa only [HasPowerExponent,Function.comp_def,id_eq] using
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (Real.tendsto_log_atTop.comp hY)

def logarithmicBoxLoss (t : ℕ) (H K Y : ℝ) : ℝ :=
  ((⌊Real.log (Y^H/Y^(-K))⌋₊+1:ℕ)^t:ℝ)*(Real.exp 1)^(2*t)

lemma logarithmicBoxLoss_exponent (t : ℕ) {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    {Y : ℕ → ℝ} (hY : Tendsto Y atTop atTop) (hY₁ : ∀ j, 1 < Y j) :
    HasPowerExponent Y (fun j => logarithmicBoxLoss t H K (Y j)) 0 := by
  let c : ℝ := 1+H+K
  have hc : 0 < c := by dsimp [c]; positivity
  have hlogp : ∀ᶠ j in atTop, 0 < Real.log (Y j) :=
    Eventually.of_forall (fun j => Real.log_pos (hY₁ j))
  have hg : HasPowerExponent Y (fun j => 1+c*Real.log (Y j)) 0 := by
    simpa only [max_self] using (HasPowerExponent.const hY 1).add
      ((HasPowerExponent.logarithm hY).const_mul hY hc hlogp) hY
      (Eventually.of_forall (fun _ => zero_lt_one))
      (by filter_upwards [hlogp] with j hj using mul_pos hc hj)
  have hgp : ∀ᶠ j in atTop, 0 < 1+c*Real.log (Y j) := by
    filter_upwards [hlogp] with j hj
    positivity
  have hUpper : HasPowerExponent Y
      (fun j => (Real.exp 1)^(2*t)*(1+c*Real.log (Y j))^t) 0 := by
    simpa only [mul_zero] using (hg.natPow t).const_mul hY (pow_pos (Real.exp_pos _) _) 
      (by filter_upwards [hgp] with j hj using pow_pos hj t)
  have hb (j : ℕ) : 1 ≤ logarithmicBoxLoss t H K (Y j) ∧
      logarithmicBoxLoss t H K (Y j) ≤ (Real.exp 1)^(2*t)*(1+c*Real.log (Y j))^t := by
    have hYp : 0 < Y j := lt_trans zero_lt_one (hY₁ j)
    have hlog : 0 ≤ Real.log (Y j) := (Real.log_pos (hY₁ j)).le
    have he : Real.log ((Y j)^H/(Y j)^(-K)) = (H+K)*Real.log (Y j) := by
      rw [Real.log_div (Real.rpow_pos_of_pos hYp _).ne' (Real.rpow_pos_of_pos hYp _).ne',
        Real.log_rpow hYp,Real.log_rpow hYp]
      ring
    have hn : (1:ℝ) ≤ (⌊Real.log ((Y j)^H/(Y j)^(-K))⌋₊+1:ℕ) := by
      exact_mod_cast Nat.succ_pos _
    have hnu : ((⌊Real.log ((Y j)^H/(Y j)^(-K))⌋₊+1:ℕ):ℝ) ≤
        1+c*Real.log (Y j) := by
      push_cast
      rw [he]
      have hfloor := Nat.floor_le (mul_nonneg (add_nonneg hH hK) hlog)
      dsimp [c]
      nlinarith
    have hpow := one_le_pow₀ hn (n := t)
    have hexp := one_le_pow₀ (Real.one_le_exp_iff.mpr (show (0:ℝ) ≤ 1 by norm_num)) (n := 2*t)
    push_cast at hn hnu hpow
    constructor
    · unfold logarithmicBoxLoss
      push_cast
      nlinarith
    · unfold logarithmicBoxLoss
      push_cast
      have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans hn) hnu t)
        (pow_nonneg (Real.exp_pos 1).le (2*t))
      simpa only [mul_comm] using h
  apply (HasPowerExponent.const hY 1).squeeze' hUpper
  · filter_upwards [] with j
    simpa only [Real.log_one,zero_div] using
      div_nonneg (Real.log_nonneg (hb j).1) (Real.log_pos (hY₁ j)).le
  · filter_upwards [] with j
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (zero_lt_one.trans_le (hb j).1) (hb j).2)
      (Real.log_pos (hY₁ j)).le

end CubicFirstMoment

end

end OAI
