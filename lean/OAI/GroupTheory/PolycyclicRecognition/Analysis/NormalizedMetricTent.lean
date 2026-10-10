import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricTent
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CocycleHaarAverage

namespace OAI

/-! # Normalized inverse-coordinate metric cutoffs -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Metric Set

variable {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant]

def normalizedMetricTent (S : Set G) (r : ℝ) (x : G) : ℝ :=
  metricTent S r x⁻¹ / (∫ y, metricTent S r y ∂μ)

omit [Group G] [IsTopologicalGroup G] [IsIsometricSMul G G] [μ.IsInvInvariant] in
theorem metricTent_mass_pos {S : Set G} (hS : IsCompact S) (hne : S.Nonempty)
    (hμ : 0 < μ.real S) {r : ℝ} (hr : 0 < r) :
    0 < ∫ y, metricTent S r y ∂μ :=
  hμ.trans_le (metricTent_integral_lower μ hS hne hr)

omit [IsIsometricSMul G G] [ProperSpace G] [BorelSpace G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] in
theorem continuous_normalizedMetricTent (S : Set G) (r : ℝ) :
    Continuous (normalizedMetricTent μ S r) :=
  ((continuous_metricTent S r).comp continuous_inv).div_const _

omit [IsIsometricSMul G G] [BorelSpace G] [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] in
theorem normalizedMetricTent_compact_support {S : Set G} (hS : IsCompact S)
    (hne : S.Nonempty) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (normalizedMetricTent μ S r) := by
  have h := (metricTent_compact_support hS hne hr).comp_homeomorph (Homeomorph.inv G)
  apply h.mono
  intro x hx
  change metricTent S r x⁻¹ ≠ 0
  intro hz
  apply hx
  change metricTent S r x⁻¹ / _ = 0
  rw [hz, zero_div]

omit [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] [BorelSpace G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] in
theorem normalizedMetricTent_nonneg (S : Set G) (r : ℝ) (x : G) :
    0 ≤ normalizedMetricTent μ S r x :=
  div_nonneg (metricTent_nonneg _ _ _) (integral_nonneg (metricTent_nonneg S r))

omit [IsIsometricSMul G G] in
theorem integral_normalizedMetricTent {S : Set G} (hS : IsCompact S)
    (hne : S.Nonempty) (hμ : 0 < μ.real S) {r : ℝ} (hr : 0 < r) :
    ∫ x, normalizedMetricTent μ S r x ∂μ = 1 := by
  simp only [normalizedMetricTent]
  rw [integral_div, integral_inv_eq_self]
  exact div_self (metricTent_mass_pos μ hS hne hμ hr).ne'

omit [IsTopologicalGroup G] [μ.IsInvInvariant] in
theorem normalizedMetricTent_translation_bound {S : Set G} (hS : IsCompact S)
    (hne : S.Nonempty) (hμ : 0 < μ.real S) {r : ℝ} (hr : 0 < r) (q x : G) :
    |normalizedMetricTent μ S r (q⁻¹ * x) - normalizedMetricTent μ S r x| ≤
      dist 1 q / (r * (∫ y, metricTent S r y ∂μ)) := by
  have hmass := metricTent_mass_pos μ hS hne hμ hr
  have hd : dist (x⁻¹ * q) x⁻¹ = dist 1 q := by
    simpa only [mul_one, dist_comm] using dist_mul_left x⁻¹ q (1 : G)
  calc
    _ = |metricTent S r (x⁻¹ * q) - metricTent S r x⁻¹| /
        (∫ y, metricTent S r y ∂μ) := by
      simp only [normalizedMetricTent, mul_inv_rev, inv_inv, ← sub_div, abs_div,
        abs_of_pos hmass]
    _ ≤ (dist 1 q / r) / (∫ y, metricTent S r y ∂μ) :=
      div_le_div_of_nonneg_right (by simpa only [hd] using abs_metricTent_sub_le S hr (x⁻¹ * q) x⁻¹)
        hmass.le
    _ = _ := by rw [div_div]

omit [IsTopologicalGroup G] [ProperSpace G] [BorelSpace G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsInvInvariant] in
theorem normalizedMetricTent_translation_support {S : Set G} (hS : S.Nonempty)
    {r : ℝ} (hr : 0 < r) {q : G} (hq : dist 1 q ≤ r) :
    Function.support (fun x => normalizedMetricTent μ S r (q⁻¹ * x) -
      normalizedMetricTent μ S r x) ⊆ Inv.inv ⁻¹' cthickening (2 * r) S := by
  intro x hx
  have ht : infDist x⁻¹ S < 2 * r := by
    by_cases h0 : metricTent S r x⁻¹ = 0
    · have h1 : metricTent S r (x⁻¹ * q) ≠ 0 := by
        intro hh
        exact hx (by simp [normalizedMetricTent, mul_inv_rev, h0, hh])
      have hp : 0 < metricTent S r (x⁻¹ * q) :=
        lt_of_le_of_ne (metricTent_nonneg _ _ _) h1.symm
      have hi : infDist (x⁻¹ * q) S < r := by
        have he := (lt_max_iff.mp hp).resolve_right (lt_irrefl 0)
        exact (div_lt_one hr).1 (by linarith)
      have hd : dist x⁻¹ (x⁻¹ * q) = dist 1 q := by
        simpa only [mul_one] using dist_mul_left x⁻¹ (1 : G) q
      have hdist := infDist_le_infDist_add_dist (s := S) (x := x⁻¹) (y := x⁻¹ * q)
      rw [hd] at hdist
      linarith
    · have hp := lt_of_le_of_ne (metricTent_nonneg S r x⁻¹) (Ne.symm h0)
      have he := (lt_max_iff.mp hp).resolve_right (lt_irrefl 0)
      have hi := (div_lt_one hr).1 (show infDist x⁻¹ S / r < 1 by linarith)
      linarith
  exact thickening_subset_cthickening _ S ((mem_thickening_iff_infDist_lt hS).2 ht)

theorem normalizedMetricTent_translation_integral_le {S : Set G} (hS : IsCompact S)
    (hne : S.Nonempty) (hμ : 0 < μ.real S) {r : ℝ} (hr : 0 < r)
    {q : G} (hq : dist 1 q ≤ r) :
    (∫ x, |normalizedMetricTent μ S r (q⁻¹ * x) - normalizedMetricTent μ S r x| ∂μ) ≤
      dist 1 q / (r * (∫ y, metricTent S r y ∂μ)) * μ.real (cthickening (2 * r) S) := by
  let f := fun x => |normalizedMetricTent μ S r (q⁻¹ * x) - normalizedMetricTent μ S r x|
  let K := Inv.inv ⁻¹' cthickening (2 * r) S
  have hK : IsCompact K := (Homeomorph.inv G).isClosedEmbedding.isCompact_preimage hS.cthickening
  have he : (∫ x in K, f x ∂μ) = ∫ x, f x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      have hz : normalizedMetricTent μ S r (q⁻¹ * x) - normalizedMetricTent μ S r x = 0 := by
        by_contra hz
        exact hx (normalizedMetricTent_translation_support μ hne hr hq hz)
      exact abs_eq_zero.mpr hz)
  have hbound := norm_setIntegral_le_of_norm_le_const (f := f) (μ := μ) (s := K) hK.measure_lt_top
    (fun x (_hx : x ∈ K) => by
      simpa only [f, Real.norm_eq_abs, abs_abs] using
        normalizedMetricTent_translation_bound μ hS hne hμ hr q x)
  rw [he, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => abs_nonneg _))] at hbound
  have hmeasure : μ.real K = μ.real (cthickening (2 * r) S) :=
    congrArg ENNReal.toReal (Measure.measure_preimage_inv μ _)
  simpa only [hmeasure] using hbound

end PolycyclicRecognition

end

end OAI
