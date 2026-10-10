import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedMetricTent
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledReiterCocycles

namespace OAI

/-! # Compact Følner pairs supply controlled averaging densities

Only a bounded volume ratio between a compact set and its thickening is
needed. Normalized inverse-coordinate tents produce continuous probability
densities with the required support and translation estimates.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric Set Filter

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]

structure ControlledMetricFolnerPairs (μ : Measure G) where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_tendsto : Tendsto scale atTop atTop
  sets : ℕ → Set G
  compact : ∀ n, IsCompact (sets n)
  nonempty : ∀ n, (sets n).Nonempty
  positive : ∀ n, 0 < μ.real (sets n)
  radiusConstant : ℝ
  radius_nonneg : 0 ≤ radiusConstant
  radius_bound : ∀ n x, x ∈ sets n → dist 1 x ≤ radiusConstant * scale n
  volumeConstant : ℝ
  volume_nonneg : 0 ≤ volumeConstant
  volume_bound : ∀ n, μ.real (cthickening (2 * scale n) (sets n)) ≤
    volumeConstant * μ.real (sets n)

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant]

def ControlledMetricFolnerPairs.toReiter (F : ControlledMetricFolnerPairs μ) :
    ControlledReiterFamily μ (fun g => dist 1 g) where
  scale := F.scale
  scale_pos := F.scale_pos
  scale_tendsto := F.scale_tendsto
  weight n := normalizedMetricTent μ (F.sets n) (F.scale n)
  continuous_weight n := continuous_normalizedMetricTent μ _ _
  compact_support n := normalizedMetricTent_compact_support μ (F.compact n)
    (F.nonempty n) (F.scale_pos n)
  nonneg n x := normalizedMetricTent_nonneg μ _ _ x
  mass n := integral_normalizedMetricTent μ (F.compact n) (F.nonempty n)
    (F.positive n) (F.scale_pos n)
  control Q hQ := by
    obtain ⟨D₀, hD₀⟩ := hQ.exists_bound_of_continuousOn
      (continuous_const.dist continuous_id).continuousOn
    let D := max D₀ 0
    have hD : 0 ≤ D := le_max_right _ _
    have hdist (q : G) (hq : q ∈ Q) : dist 1 q ≤ D := by
      have h := hD₀ q hq
      simpa only [D, id_eq, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using
        h.trans (le_max_left D₀ 0)
    refine ⟨F.radiusConstant + 2, D * F.volumeConstant, by linarith [F.radius_nonneg],
      mul_nonneg hD F.volume_nonneg, ?_⟩
    filter_upwards [F.scale_tendsto.eventually (eventually_ge_atTop D)] with n hn
    intro q hq
    have hr := F.scale_pos n
    have hqr : dist 1 q ≤ F.scale n := (hdist q hq).trans hn
    have hm := metricTent_mass_pos μ (F.compact n) (F.nonempty n) (F.positive n) hr
    refine ⟨?_, ?_⟩
    · intro x hx
      have hmem := normalizedMetricTent_translation_support μ (F.nonempty n) hr hqr hx
      change infEDist x⁻¹ (F.sets n) ≤ ENNReal.ofReal (2 * F.scale n) at hmem
      have hi : infDist x⁻¹ (F.sets n) ≤ 2 * F.scale n := by
        have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmem
        simpa only [infDist, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * F.scale n)] using h
      obtain ⟨y, hy, he⟩ := (F.compact n).exists_infDist_eq_dist (F.nonempty n) x⁻¹
      have hinv : dist 1 x = dist 1 x⁻¹ := by
        calc
          dist 1 x = dist x⁻¹ 1 := by
            simpa only [mul_one, inv_mul_cancel] using (dist_mul_left x⁻¹ (1 : G) x).symm
          _ = dist 1 x⁻¹ := dist_comm _ _
      rw [hinv]
      have htri := dist_triangle (1 : G) y x⁻¹
      rw [dist_comm y x⁻¹, ← he] at htri
      have hyb := F.radius_bound n y hy
      nlinarith
    · have hfirst := normalizedMetricTent_translation_integral_le μ (F.compact n)
        (F.nonempty n) (F.positive n) hr hqr
      have hvolume : μ.real (cthickening (2 * F.scale n) (F.sets n)) ≤
          F.volumeConstant * (∫ y, metricTent (F.sets n) (F.scale n) y ∂μ) :=
        (F.volume_bound n).trans (mul_le_mul_of_nonneg_left
          (metricTent_integral_lower μ (F.compact n) (F.nonempty n) hr) F.volume_nonneg)
      calc
        _ ≤ dist 1 q / (F.scale n * (∫ y, metricTent (F.sets n) (F.scale n) y ∂μ)) *
            μ.real (cthickening (2 * F.scale n) (F.sets n)) := hfirst
        _ ≤ D / (F.scale n * (∫ y, metricTent (F.sets n) (F.scale n) y ∂μ)) *
            (F.volumeConstant * (∫ y, metricTent (F.sets n) (F.scale n) y ∂μ)) :=
          mul_le_mul (div_le_div_of_nonneg_right (hdist q hq) (by positivity)) hvolume
            ENNReal.toReal_nonneg (by positivity)
        _ = (D * F.volumeConstant) / F.scale n := by field_simp

end PolycyclicRecognition

end

end OAI
