import OAI.NumberTheory.TotientAsymptotic.PrimeWindow

namespace OAI

/-! Prime counts at both moving endpoints of the least-preimage interval. -/

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem linear_prime_window (hpnt : PrimeNumberTheoremInput)
    {a b ε : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D y : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) →
      a*x/D ≤ y → y ≤ b*x/D →
      |(Nat.primeCounting ⌊y⌋₊ : ℝ)-y/Real.log x| ≤ ε*x/(D*Real.log x) := by
  let δ := min (1/4 : ℝ) (ε/(6*b))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδq : δ ≤ 1/4 := min_le_left _ _
  have hδb : 6*δ*b ≤ ε := by
    have hh := (le_div_iff₀ (show 0 < 6*b by positivity)).mp (min_le_right (1/4 : ℝ) (ε/(6*b)))
    nlinarith
  have hlow : Tendsto (fun x : ℝ => (Real.log x)^(4/5 : ℝ)/Real.log x+
      (-Real.log a)/Real.log x) atTop (nhds 0) := by
    simpa using subpower_log_ratio.add (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
  have hupp : Tendsto (fun x : ℝ => Real.log b/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  obtain ⟨Y,hY⟩ := eventually_atTop.mp (hpnt δ hδ)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hlow.eventually (eventually_lt_nhds hδ),hupp.eventually (eventually_lt_nhds hδ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).eventually (eventually_ge_atTop Y)]
    with x hx hlo hup hYx
  intro D y hD hlogD hylo hyhi
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hy0 : 0 < y := (div_pos (mul_pos ha hx0) hD0).trans_le hylo
  have hloglo : (1-δ)*Real.log x ≤ Real.log y := by
    have hh := (div_lt_iff₀ hL).mp (show ((Real.log x)^(4/5 : ℝ)-Real.log a)/Real.log x < δ by
      convert hlo using 1; ring)
    have ht := Real.log_le_log (div_pos (mul_pos ha hx0) hD0) hylo
    rw [Real.log_div (mul_pos ha hx0).ne' hD0.ne',Real.log_mul ha.ne' hx0.ne'] at ht
    linarith
  have hloghi : Real.log y ≤ (1+δ)*Real.log x := by
    have hxy : y ≤ b*x := hyhi.trans (div_le_self (mul_nonneg hb.le hx0.le) hD)
    have ht := Real.log_le_log hy0 hxy
    rw [Real.log_mul hb.ne' hx0.ne'] at ht
    have hh := (div_lt_iff₀ hL).mp hup
    linarith
  have hroot : x^(1/2 : ℝ) ≤ y := by
    rw [Real.rpow_def_of_pos hx0]
    calc
      _ ≤ Real.exp (Real.log y) := Real.exp_le_exp.mpr (by nlinarith)
      _ = y := Real.exp_log hy0
  have hp := hY y (hYx.trans hroot)
  have he := prime_count_change_scale hL hy0.le hδ.le hδq ⟨hloglo,hloghi⟩
    ⟨le_rfl,le_mul_of_one_le_left hy0.le (by linarith : 1 ≤ 1+δ)⟩ hp
  apply he.trans
  calc
    6*δ*(y/Real.log x) ≤ 6*δ*((b*x/D)/Real.log x) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hyhi hL.le) (by positivity)
    _ = (6*δ*b)*x/(D*Real.log x) := by ring
    _ ≤ ε*x/(D*Real.log x) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hδb hx0.le) (mul_nonneg hD0.le hL.le)

end TotientAsymptotic

end

end OAI
