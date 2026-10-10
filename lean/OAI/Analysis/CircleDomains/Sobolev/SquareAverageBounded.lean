import OAI.Analysis.CircleDomains.Uniformization.SquareAverageLimit
import Mathlib.MeasureTheory.Covering.DensityTheorem

namespace OAI

/-! Integrable fields have finite centered-square maximal averages
almost everywhere. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma abs_squareAverage_le_global_integral {g : ℝ × ℝ → ℝ}
    (hg : Integrable g volume) (x : ℝ × ℝ) {r : ℝ} (hr : 0 < r) :
    |squareAverage g x r| ≤ (4*r^2)⁻¹ * (∫ p, |g p|) := by
  apply (abs_average_le_average_abs (volume.restrict (coordinateSquare x r)) g).trans
  rw [average_eq, measureReal_restrict_apply_univ, coordinateSquare_real_volume x hr.le,
    smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ => abs_nonneg _) hg.abs)
    (by positivity)

lemma ae_squareAverage_bounded {g : ℝ × ℝ → ℝ} (hg : Integrable g volume) :
    ∀ᵐ x ∂volume, ∃ B : ℝ, 0 ≤ B ∧ ∀ r > 0, squareAverage g x r ≤ B := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume hg.locallyIntegrable 1] with x hx
  have hl : Tendsto (fun r : ℝ => squareAverage g x r) (𝓝[>] 0) (𝓝 (g x)) := by
    apply hx (fun _ => x) id tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mem_closedBall_self (by simpa only [one_mul] using hr.le)
  have he : ∀ᶠ r in 𝓝[>] (0:ℝ), squareAverage g x r < g x+1 :=
    hl (Iio_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp he
  let B := max (|g x|+1) ((4*δ^2)⁻¹ * (∫ p, |g p|))
  refine ⟨B, (by dsimp only [B]; positivity), ?_⟩
  intro r hr
  by_cases hrd : r < δ
  · have hs : squareAverage g x r < g x+1 := hsmall ⟨?_, hr⟩
    · calc
        _ ≤ g x+1 := hs.le
        _ ≤ |g x|+1 := by linarith [le_abs_self (g x)]
        _ ≤ B := le_max_left _ _
    · simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using hrd
  · have hdr : δ ≤ r := le_of_not_gt hrd
    apply le_trans (le_abs_self _) ((abs_squareAverage_le_global_integral hg x hr).trans ?_)
    apply le_trans ?_ (le_max_right _ _)
    apply mul_le_mul_of_nonneg_right _ (integral_nonneg fun _ => abs_nonneg _)
    apply inv_anti₀ (by positivity)
    nlinarith [mul_self_le_mul_self hδ.le hdr]

end CircleDomainRigidity

end

end OAI
