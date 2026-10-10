import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.GlobalGrowth

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem global_growth_mass_le_ediam_power {n d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hg : GlobalUpperGrowth n G μ)
    (A : Set (Ambient d)) (hfinite : ediam A ≠ ⊤) :
    μ A ≤ ENNReal.ofReal G * ediam A ^ n := by
  rcases eq_empty_or_nonempty A with (rfl | ⟨x, hx⟩)
  · simp only [measure_empty, zero_le]
  let δ := diam A
  have hδ : 0 ≤ δ := diam_nonneg
  have hc : Continuous (fun r : ℝ => ENNReal.ofReal (G * r ^ n)) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_id.pow n))
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (G * r ^ n))
      (𝓝[>] δ) (𝓝 (ENNReal.ofReal (G * δ ^ n))) := hc.continuousWithinAt.tendsto
  have hb : ∀ᶠ r in 𝓝[>] δ, μ A ≤ ENNReal.ofReal (G * r ^ n) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hδr : δ < r := hr
    have hsub : A ⊆ ball x r := by
      intro y hy
      exact (dist_le_diam_of_mem' hfinite hy hx).trans_lt hδr
    exact (measure_mono hsub).trans (hg.2 x r (hδ.trans_lt hδr))
  have h := ge_of_tendsto hlim hb
  have heq : ENNReal.ofReal (G * δ ^ n) = ENNReal.ofReal G * ediam A ^ n := by
    rw [ENNReal.ofReal_mul hg.1, ENNReal.ofReal_pow hδ]
    change ENNReal.ofReal G * (ENNReal.ofReal (ediam A).toReal) ^ n = _
    rw [ENNReal.ofReal_toReal hfinite]
  exact h.trans_eq heq

theorem global_growth_le_hausdorffMeasure {n d : ℕ}
    (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ) :
    μ ≤ ENNReal.ofReal G • (μH[(n : ℝ)] : Measure (Ambient d)) := by
  have hμ : μ ≤ Measure.mkMetric (fun r : ℝ≥0∞ => ENNReal.ofReal G * r ^ n) := by
    apply Measure.le_mkMetric _ μ 1 (by norm_num)
    intro A hA
    exact global_growth_mass_le_ediam_power μ G hg A (ne_top_of_le_ne_top (by norm_num) hA)
  apply hμ.trans
  change (Measure.mkMetric (fun r : ℝ≥0∞ => ENNReal.ofReal G * r ^ n) : Measure (Ambient d)) ≤
    ENNReal.ofReal G • Measure.mkMetric (fun r : ℝ≥0∞ => r ^ (n : ℝ))
  apply Measure.mkMetric_mono_smul ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.mpr hG).ne'
  exact Filter.Eventually.of_forall (fun r => by
    simp only [Pi.smul_apply, smul_eq_mul, ENNReal.rpow_natCast, le_refl])

end

end RieszRectifiability

end OAI
