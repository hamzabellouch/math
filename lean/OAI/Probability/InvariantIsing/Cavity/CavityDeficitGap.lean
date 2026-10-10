import OAI.Probability.InvariantIsing.Spectral.SpectralDeficitDerivative

namespace OAI

/-! On a gap in the finite overlap support, the deficit is affine with
slope equal to minus the mass below the gap. Endpoints may be atoms. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma deficit_antitone_argument (p : OverlapPath) : Antitone (deficit p) := by
  intro a b hab
  rw [deficit_eq_integral, deficit_eq_integral]
  apply integral_mono (p.integrable_complement_max b) (p.integrable_complement_max a)
  intro s
  exact sub_le_sub_left (max_le_max_left (p s) hab) 1

lemma deficit_lower_of_ae_le (p : OverlapPath) {M r : ℝ}
    (hM : ∀ᵐ s ∂pathMeasure, p s ≤ M) (hr : r ≤ M) :
    1 - M ≤ deficit p r := by
  rw [deficit_eq_integral]
  calc
    1 - M = ∫ _s : ℝ, (1 - M) ∂pathMeasure := by simp
    _ ≤ ∫ s, 1 - max (p s) r ∂pathMeasure := by
      apply integral_mono_ae (integrable_const _) (p.integrable_complement_max r)
      filter_upwards [hM] with s hs
      exact sub_le_sub_left (max_le hs hr) 1

lemma deficit_constant_below_ae_lower (p : OverlapPath) {a r : ℝ}
    (ha : ∀ᵐ s ∂pathMeasure, a ≤ p s) (hr : r ≤ a) :
    deficit p r = deficit p a := by
  rw [deficit_eq_integral, deficit_eq_integral]
  apply integral_congr_ae
  filter_upwards [ha] with s hs
  rw [max_eq_left (hr.trans hs), max_eq_left hs]

theorem deficit_affine_on_gap (p : OverlapPath) {a b : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s)
    {r : ℝ} (hr : r ∈ Icc a b) :
    deficit p r = deficit p a - pathMeasure.real {s | p s ≤ a} * (r - a) := by
  let A : Set ℝ := {s | p s ≤ a}
  have hA : MeasurableSet A := measurableSet_le p.measurable measurable_const
  have he : (fun s => (1 - max (p s) r) - (1 - max (p s) a)) =ᵐ[pathMeasure]
      A.indicator (fun _ => a - r) := by
    filter_upwards [hgap] with s hs
    by_cases hsa : p s ≤ a
    · rw [max_eq_right (hsa.trans hr.1), max_eq_right hsa,
        indicator_of_mem (show s ∈ A from hsa)]
      ring
    · have hbs : b ≤ p s := hs.resolve_left hsa
      rw [max_eq_left (hr.2.trans hbs), max_eq_left (hr.1.trans (hr.2.trans hbs)),
        indicator_of_notMem (show s ∉ A from hsa)]
      ring
  have hi : deficit p r - deficit p a = pathMeasure.real A * (a - r) := by
    rw [deficit_eq_integral, deficit_eq_integral,
      ← integral_sub (p.integrable_complement_max r) (p.integrable_complement_max a),
      integral_congr_ae he, integral_indicator_const (a - r) hA]
    rfl
  change deficit p r = deficit p a - pathMeasure.real A * (r - a)
  linarith

theorem hasDerivAt_deficit_on_gap (p : OverlapPath) {a b r : ℝ}
    (hgap : ∀ᵐ s ∂pathMeasure, p s ≤ a ∨ b ≤ p s) (hr : r ∈ Ioo a b) :
    HasDerivAt (deficit p) (-pathMeasure.real {s | p s ≤ a}) r := by
  have hd : HasDerivAt
      (fun t => deficit p a - pathMeasure.real {s | p s ≤ a} * (t - a))
      (-pathMeasure.real {s | p s ≤ a}) r := by
    convert! (((hasDerivAt_id r).sub_const a).const_mul
      (pathMeasure.real {s | p s ≤ a})).const_sub (deficit p a) using 1
    ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  exact deficit_affine_on_gap p hgap ⟨ht.1.le, ht.2.le⟩

end InvariantIsing

end

end OAI
