import OAI.NumberTheory.JointDickman.Arithmetic.PrimeProductLocalLaw
import OAI.NumberTheory.JointDickman.Arithmetic.RoughDensityRegularity

namespace OAI

/-! # Positive local mass for the selected coefficient product -/

namespace JointDickman

open Filter Finset MeasureTheory
open scoped Topology

theorem half_density_compact_lower
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1 / 2)) (H : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ s : ℝ, 1 ≤ s → s ≤ 3 →
      d ≤ scaledRoughDensity c (1 / 2) H B s := by
  let k := (4 : ℝ)^(-(1 / 2 : ℝ)) *
    (Real.exp (-Real.eulerMascheroniConstant * (1 / 2)) / Real.Gamma (1 / 2))
  let d := k * (3 : ℝ)^(-(1 / 2 : ℝ)) / 2
  have hk : 0 < k := mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (div_pos (Real.exp_pos _) (Real.Gamma_pos_of_pos (by norm_num)))
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d, hd, ?_⟩
  have hu := scaledRoughDensity_tendstoUniformlyOn hM hMP c hc
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) < 1) H
  have he := (Metric.tendstoUniformlyOn_iff.mp hu) d hd
  filter_upwards [he] with B hb
  intro s hs hs3
  have hc' := hb s hs
  rw [Real.dist_eq] at hc'
  have hp := Real.rpow_le_rpow_of_nonpos (by linarith only [hs] : 0 < s) hs3
    (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  have hm := mul_le_mul_of_nonneg_left hp hk.le
  have hexp : (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) := by norm_num
  rw [hexp] at hc'
  change |k * s^(-(1 / 2 : ℝ)) - scaledRoughDensity c (1 / 2) H B s| < d at hc'
  dsimp only [d] at hc' ⊢
  nlinarith only [hm, (abs_lt.mp hc').2]

/-- Uniform lower mass on every logarithmic interval inside [1,3]. The
fixed B⁻⁸⁰ error is retained so the theorem also applies to intervals of
length comparable to 1/B. -/
theorem half_primeProduct_interval_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d E : ℝ, 0 < d ∧ 0 < E ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
      1 ≤ a → a ≤ b → b ≤ 3 →
      d * (b - a) - E * (B : ℝ)^(-(80 : ℝ)) ≤
        ∑ n ∈ Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊,
          primeProductMass (auxiliaryPrimes B) (1 / 2) n := by
  obtain ⟨c, hc, _, H, E, hE, hlocal⟩ := primeProduct_local_interval_law hSD hM
    (Or.inr rfl : (1 / 2 : ℝ) = 1 / 4 ∨ (1 / 2 : ℝ) = 1 / 2)
  obtain ⟨d, hd, hdensity⟩ := half_density_compact_lower hM hMP c hc H
  refine ⟨d, E, hd, hE, ?_⟩
  filter_upwards [hlocal, hdensity, eventually_ge_atTop 1] with B hl hdB hB
  intro a b ha hab hb
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hp : (B : ℝ)^(-(1 / 10 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hB1 (by norm_num)
  have hloc := hl a b (hp.trans ha) hab (by linarith only [hb])
  have hi : IntervalIntegrable (scaledRoughDensity c (1 / 2) H B) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact (hasDerivAt_scaledRoughDensity c (1 / 2) H B
      (by linarith only [ha, hs.1] : 0 < s)).continuousAt.continuousWithinAt
  have hilow := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := d)) hi (fun s hs => hdB s (ha.trans hs.1) (hs.2.trans hb))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hilow
  nlinarith only [hilow, (abs_le.mp hloc).1]

/-- Positive mass persists at the multiplicative-window scale: an interval
of logarithmic width at least h/B has mass at least a fixed multiple of 1/B. -/
theorem half_primeProduct_short_interval_lower
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) {h : ℝ} (hh : 0 < h) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ B : ℕ in atTop, ∀ a b : ℝ,
      1 ≤ a → a ≤ b → b ≤ 3 → h / B ≤ b - a →
      d / B ≤ ∑ n ∈ Ioc ⌊Real.exp (B * a)⌋₊ ⌊Real.exp (B * b)⌋₊,
        primeProductMass (auxiliaryPrimes B) (1 / 2) n := by
  obtain ⟨d, E, hd, _, hbound⟩ := half_primeProduct_interval_lower hSD hM hMP
  refine ⟨d * h / 2, by positivity, ?_⟩
  have hlim : Tendsto (fun B : ℕ => E * (B : ℝ)^(-(79 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 79)).comp
        tendsto_natCast_atTop_atTop).const_mul E)
  have hsmall := hlim.eventually (eventually_le_nhds (by positivity : (0 : ℝ) < d * h / 2))
  filter_upwards [hbound, hsmall, eventually_gt_atTop 0] with B hb hs hB
  intro a b ha hab hb3 hwidth
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hw := mul_le_mul_of_nonneg_left ((div_le_iff₀ hB0).mp hwidth) hd.le
  have hmain := mul_le_mul_of_nonneg_right (hb a b ha hab hb3) hB0.le
  have heq : E * (B : ℝ)^(-(80 : ℝ)) * B = E * (B : ℝ)^(-(79 : ℝ)) := by
    rw [show (-(79 : ℝ)) = -80 + 1 by norm_num, Real.rpow_add hB0, Real.rpow_one]
    ring
  rw [sub_mul, heq] at hmain
  apply (div_le_iff₀ hB0).mpr
  nlinarith only [hw, hmain, hs]

end JointDickman

end OAI
