import OAI.Probability.GammaPassage.Quantile
import Mathlib.Topology.Order.Basic

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

noncomputable def gammaSurvival (shape rate x : ℝ) : ℝ :=
  1 - cdf (gammaMeasure shape rate) x

noncomputable def gammaSurvivalQuantile (v : ℝ) : ℝ :=
  gammaQuantileReal shape rate hs hr (1 - v)

noncomputable def gammaSurvivalQuantileExtended (v : ℝ) : ℝ≥0∞ :=
  gammaQuantileExtended shape rate hs hr (1 - v)

lemma gammaSurvival_mem (hs : 0 < shape) (hr : 0 < rate) {x : ℝ} (hx : 0 ≤ x) :
    gammaSurvival shape rate x ∈ Ioc (0 : ℝ) 1 := by
  have h := gamma_cdf_lt_one hs hr hx
  have h' := cdf_nonneg (gammaMeasure shape rate) x
  constructor <;> dsimp [gammaSurvival] <;> linarith

lemma gammaQuantileReal_cdf {x : ℝ} (hx : 0 ≤ x) :
    gammaQuantileReal shape rate hs hr (cdf (gammaMeasure shape rate) x) = x := by
  have hq := gammaQuantileReal_spec hs hr (cdf_nonneg _ x) (gamma_cdf_lt_one hs hr hx)
  exact (gamma_cdf_strictMonoOn hs hr).injOn hq.1 hx hq.2

lemma gammaSurvivalQuantile_inverse {x : ℝ} (hx : 0 ≤ x) :
    gammaSurvivalQuantile hs hr (gammaSurvival shape rate x) = x := by
  simpa [gammaSurvivalQuantile, gammaSurvival] using gammaQuantileReal_cdf hs hr hx

lemma gammaSurvivalQuantile_antitoneOn :
    AntitoneOn (gammaSurvivalQuantile hs hr) (Ioc (0 : ℝ) 1) := by
  intro v hv w hw hvw
  have hvq := gammaQuantileReal_spec hs hr (show 0 ≤ 1-v by linarith [hv.2])
    (show 1-v < 1 by linarith [hv.1])
  apply (gammaQuantileReal_le_iff hs hr (show 0 ≤ 1-w by linarith [hw.2])
    (show 1-w < 1 by linarith [hw.1]) hvq.1).mpr
  rw [hvq.2]
  linarith

/-- Inverse continuity includes the one-sided probability endpoint zero.
The arbitrary real value at probability one is not used. -/
lemma gammaQuantileReal_continuousOn :
    ContinuousOn (gammaQuantileReal shape rate hs hr) (Ico (0 : ℝ) 1) := by
  intro u hu
  have hq := gammaQuantileReal_spec hs hr hu.1 hu.2
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : 0 ≤ a
    · have hc : cdf (gammaMeasure shape rate) a < u := by
        have h := gamma_cdf_strictMonoOn hs hr ha0 hq.1 ha
        simpa only [hq.2] using h
      have he : ∀ᶠ v in 𝓝[Ico (0 : ℝ) 1] u, cdf (gammaMeasure shape rate) a < v :=
        (continuousWithinAt_id.tendsto).eventually (Ioi_mem_nhds hc)
      filter_upwards [he, self_mem_nhdsWithin] with v hv hvdom
      apply lt_of_not_ge
      intro hle
      have hh := (gammaQuantileReal_le_iff hs hr hvdom.1 hvdom.2 ha0).mp hle
      exact (not_le_of_gt hv) hh
    · exact Filter.Eventually.of_forall (fun v =>
        (lt_of_not_ge ha0).trans_le (gammaQuantileReal_nonneg hs hr v))
  · intro b hb
    have hb0 : 0 ≤ b := hq.1.trans hb.le
    have hc : u < cdf (gammaMeasure shape rate) b := by
      have h := gamma_cdf_strictMonoOn hs hr hq.1 hb0 hb
      simpa only [hq.2] using h
    have he : ∀ᶠ v in 𝓝[Ico (0 : ℝ) 1] u, v < cdf (gammaMeasure shape rate) b :=
      (continuousWithinAt_id.tendsto).eventually (Iio_mem_nhds hc)
    filter_upwards [he, self_mem_nhdsWithin] with v hv hvdom
    apply lt_of_not_ge
    intro hle
    have hh := monotone_cdf (gammaMeasure shape rate) hle
    rw [(gammaQuantileReal_spec hs hr hvdom.1 hvdom.2).2] at hh
    exact (not_le_of_gt hv) hh

lemma gammaSurvivalQuantile_continuousOn :
    ContinuousOn (gammaSurvivalQuantile hs hr) (Ioc (0 : ℝ) 1) := by
  apply (gammaQuantileReal_continuousOn hs hr).comp
    (continuous_const.sub continuous_id).continuousOn
  intro v hv
  constructor <;> dsimp <;> linarith [hv.1, hv.2]

lemma gammaSurvivalQuantileExtended_zero :
    gammaSurvivalQuantileExtended hs hr 0 = ⊤ := by
  simpa [gammaSurvivalQuantileExtended] using gammaQuantileExtended_one hs hr

lemma gammaSurvivalQuantileExtended_of_pos {v : ℝ} (hv : 0 < v) :
    gammaSurvivalQuantileExtended hs hr v =
      ENNReal.ofReal (gammaSurvivalQuantile hs hr v) := by
  have hn : 1-v ≠ 1 := by linarith
  simp [gammaSurvivalQuantileExtended, gammaQuantileExtended, hn, gammaSurvivalQuantile]

/-- On the finite-bit domain, the infinity guard is exactly positive survival. -/
lemma gammaSurvivalQuantileExtended_ne_top_iff {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    gammaSurvivalQuantileExtended hs hr v ≠ ⊤ ↔ 0 < v := by
  constructor
  · intro h
    by_contra hn
    have hz : v = 0 := le_antisymm (le_of_not_gt hn) hv.1
    subst v
    exact h (gammaSurvivalQuantileExtended_zero hs hr)
  · intro h
    rw [gammaSurvivalQuantileExtended_of_pos hs hr h]
    exact ENNReal.ofReal_ne_top

lemma gammaSurvivalQuantileExtended_toReal {v : ℝ} (hv : 0 < v) :
    (gammaSurvivalQuantileExtended hs hr v).toReal = gammaSurvivalQuantile hs hr v := by
  rw [gammaSurvivalQuantileExtended_of_pos hs hr hv]
  exact ENNReal.toReal_ofReal (gammaQuantileReal_nonneg hs hr (1-v))

lemma gammaSurvivalQuantileExtended_antitoneOn :
    AntitoneOn (gammaSurvivalQuantileExtended hs hr) (Icc (0 : ℝ) 1) := by
  intro v hv w hw hvw
  by_cases hv0 : v = 0
  · subst v
    rw [gammaSurvivalQuantileExtended_zero hs hr]
    exact le_top
  · have hvp : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
    have hwp : 0 < w := hvp.trans_le hvw
    rw [gammaSurvivalQuantileExtended_of_pos hs hr hvp,
      gammaSurvivalQuantileExtended_of_pos hs hr hwp]
    exact ENNReal.ofReal_le_ofReal (gammaSurvivalQuantile_antitoneOn hs hr
      ⟨hvp, hv.2⟩ ⟨hwp, hw.2⟩ hvw)

/-- Lower survival rounding gives upper actual real cost whenever its guard holds. -/
lemma gammaSurvivalQuantile_upper_cost {x v : ℝ} (hx : 0 ≤ x)
    (hv : 0 < v) (hvs : v ≤ gammaSurvival shape rate x) :
    x ≤ gammaSurvivalQuantile hs hr v := by
  have hS := gammaSurvival_mem hs hr hx
  have h := gammaSurvivalQuantile_antitoneOn hs hr ⟨hv, hvs.trans hS.2⟩ hS hvs
  simpa only [gammaSurvivalQuantile_inverse hs hr hx] using h

end GammaFPP

end OAI
