import OAI.MeasureTheory.Falconer.Estimates.RescaledConditional

namespace OAI

/-! # Only the dyadic ball tests above the slice thickness are needed -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X] {m : ℕ}

theorem truncated_dyadic_ball_bound
    (μ : Measure X) (p : X → Space m) (N : ℕ) {a H s : ℝ}
    (ha : 1 ≤ a) (hH : 1 ≤ H) (hs : 0 ≤ s) (hmass : μ univ ≤ 1)
    (hdyadic : ∀ g ≤ N, 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g → ∀ c : Space m,
      μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} ≤
        ENNReal.ofReal (H*(1/(2:ℝ)^g)^s)) :
    ∀ (c : Space m) (r : ℝ), 1/(2:ℝ)^N ≤ r →
      μ {x | dist (p x) c ≤ r} ≤ ENNReal.ofReal (H*(4*a*r)^s) := by
  intro c r hr
  have hap : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hrp : 0 < r := (by positivity : 0 < 1/(2:ℝ)^N).trans_le hr
  by_cases hsmall : 2*a*r ≤ 1
  · have hmin : 1/(2:ℝ)^N ≤ 2*a*r := hr.trans (by nlinarith)
    obtain ⟨g,hg,hgr,hrg⟩ := Regularization.dyadic_radius_bracket hmin hsmall
    have hcut : 2*a*(1/(2:ℝ)^N) ≤ 1/(2:ℝ)^g :=
      (mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2*a)).trans hgr
    have hrad : r ≤ (1/(2:ℝ)^g)/(2*a) := (le_div_iff₀ (by positivity)).mpr (by
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hgr)
    calc
      _ ≤ μ {x | dist (p x) c ≤ (1/(2:ℝ)^g)/(2*a)} := measure_mono (fun x hx => hx.trans hrad)
      _ ≤ ENNReal.ofReal (H*(1/(2:ℝ)^g)^s) := hdyadic g hg hcut c
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by nlinarith [hrg]) hs) (by linarith))
  · apply (measure_mono (subset_univ _) |>.trans hmass).trans
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hpow : 1 ≤ (4*a*r)^s := Real.one_le_rpow (by linarith) hs
    nlinarith

end Falconer

end OAI
