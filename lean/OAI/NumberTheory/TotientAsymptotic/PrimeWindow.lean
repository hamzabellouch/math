import OAI.NumberTheory.TotientAsymptotic.PublishedPrimeCount
import OAI.NumberTheory.TotientAsymptotic.PrefixSize

namespace OAI

/-! Uniform largest-prime windows for the actual subpower prefix denominators. -/

noncomputable section
open scoped Topology
open Filter

namespace TotientAsymptotic

lemma subpower_log_ratio :
    Tendsto (fun x : ℝ => (Real.log x)^(4/5 : ℝ)/Real.log x) atTop (nhds 0) := by
  have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/5)).comp Real.tendsto_log_atTop
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  dsimp only [Function.comp_def]
  rw [show -(1/5 : ℝ) = 4/5-1 by norm_num, Real.rpow_sub (Real.log_pos hx), Real.rpow_one]

lemma small_denominator_window {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδsmall : δ ≤ 1/4) :
    ∀ᶠ x : ℝ in atTop, ∀ D t : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) → a*x ≤ t → t ≤ x →
      let z := t/D
      let y := 1+z
      x^(1/2 : ℝ) ≤ z ∧ z ≤ y ∧ y ≤ (1+δ)*z ∧
      (1-δ)*Real.log x ≤ Real.log y ∧ Real.log y ≤ (1+δ)*Real.log x := by
  have hc : Tendsto (fun x : ℝ => -Real.log a/Real.log x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have hh : Tendsto (fun x : ℝ => (Real.log x)^(4/5 : ℝ)/Real.log x +
      -Real.log a/Real.log x) atTop (nhds 0) := by
    simpa only [add_zero] using subpower_log_ratio.add hc
  have hroot : Tendsto (fun x : ℝ => x^(1/2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hh.eventually (eventually_lt_nhds hδ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log 2/δ)),
    hroot.eventually (eventually_ge_atTop (1/δ))] with x hx hsmall hlog2 hlarge
  intro D t hD hlogD ht htx
  dsimp only
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have ht0 : 0 < t := (mul_pos ha hx0).trans_le ht
  have hz0 : 0 < t/D := div_pos ht0 hD0
  have hlo : (1-δ)*Real.log x ≤ Real.log (t/D) := by
    have hb := (div_lt_iff₀ hL).mp (show ((Real.log x)^(4/5 : ℝ)-Real.log a)/Real.log x < δ by
      convert hsmall using 1; ring)
    have hlt := Real.log_le_log (mul_pos ha hx0) ht
    rw [Real.log_mul ha.ne' hx0.ne'] at hlt
    rw [Real.log_div ht0.ne' hD0.ne']
    linarith
  have hz : x^(1/2 : ℝ) ≤ t/D := by
    rw [Real.rpow_def_of_pos hx0]
    calc
      _ ≤ Real.exp (Real.log (t/D)) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := Real.exp_log hz0
  refine ⟨hz, by linarith, ?_, ?_, ?_⟩
  · have hh : 1 ≤ δ*(t/D) := by
      calc
        1 = δ*(1/δ) := by field_simp
        _ ≤ δ*(t/D) := mul_le_mul_of_nonneg_left (hlarge.trans hz) hδ.le
    linarith
  · exact hlo.trans (Real.log_le_log hz0 (by linarith))
  · have hzle : t/D ≤ x := (div_le_iff₀ hD0).mpr (by nlinarith)
    have hyle : 1+t/D ≤ 2*x := by linarith
    have hb := Real.log_le_log (by positivity : (0 : ℝ)<1+t/D) hyle
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hx0.ne'] at hb
    have h2 : Real.log 2 ≤ δ*Real.log x := by simpa only [mul_comm] using (div_le_iff₀ hδ).mp hlog2
    linarith

/-- The classical PNT is uniform over all denominators allowed by the
proved basic-witness size bound, at every fixed comparable endpoint. -/
theorem largest_prime_uniform_asymptotic (hpnt : PrimeNumberTheoremInput)
    {a : ℝ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ D t : ℝ, 1 ≤ D →
      Real.log D ≤ (Real.log x)^(4/5 : ℝ) → a*x ≤ t → t ≤ x →
      |(Nat.primeCounting ⌊1+t/D⌋₊ : ℝ)-t/(D*Real.log x)| ≤
        ε*(t/(D*Real.log x)) := by
  let δ := min (1/4 : ℝ) (ε/6)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδq : δ ≤ 1/4 := min_le_left _ _
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (hpnt δ hδ)
  filter_upwards [small_denominator_window ha hδ hδq,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).eventually (eventually_ge_atTop Y),
    eventually_gt_atTop (1 : ℝ)] with x hx hYx hx1
  intro D t hD hlogD ht htx
  obtain ⟨hz, hzy, hy, hlo, hhi⟩ := hx D t hD hlogD ht htx
  have hp := hY (1+t/D) (hYx.trans (hz.trans hzy))
  have he := prime_count_change_scale (Real.log_pos hx1)
    (div_nonneg ((mul_pos ha (zero_lt_one.trans hx1)).trans_le ht).le (by linarith))
    hδ.le hδq ⟨hlo,hhi⟩ ⟨hzy,hy⟩ hp
  rw [div_div] at he
  exact he.trans (mul_le_mul_of_nonneg_right (by dsimp [δ]; linarith [min_le_right (1/4 : ℝ) (ε/6)])
    (div_nonneg ((mul_pos ha (zero_lt_one.trans hx1)).trans_le ht).le
      (mul_nonneg (by linarith) (Real.log_pos hx1).le)))

end TotientAsymptotic

end

end OAI
