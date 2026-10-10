import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem projected_cover_le_retained_area_add_shadow
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (n : ℕ) (T : X → Y) (hT : LipschitzWith 1 T)
    (A E : Set X) (D V : Set Y)
    (hcover : D ⊆ T '' A) (hshadow : T '' (A \ E) ⊆ V) :
    (μH[(n : ℝ)] : Measure Y) D ≤
      (μH[(n : ℝ)] : Measure X) (A ∩ E) + (μH[(n : ℝ)] : Measure Y) V := by
  have hsub : D ⊆ T '' (A ∩ E) ∪ V := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hcover hy
    by_cases he : x ∈ E
    · exact Or.inl ⟨x, ⟨hx, he⟩, rfl⟩
    · exact Or.inr (hshadow ⟨x, ⟨hx, he⟩, rfl⟩)
  have harea := hT.hausdorffMeasure_image_le (show 0 ≤ (n : ℝ) by positivity) (A ∩ E)
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at harea
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add harea le_rfl))

theorem retained_area_ge_projected_cover_sub_shadow
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (n : ℕ) (T : X → Y) (hT : LipschitzWith 1 T)
    (A E : Set X) (D V : Set Y)
    (hcover : D ⊆ T '' A) (hshadow : T '' (A \ E) ⊆ V) :
    (μH[(n : ℝ)] : Measure Y) D - (μH[(n : ℝ)] : Measure Y) V ≤
      (μH[(n : ℝ)] : Measure X) (A ∩ E) := by
  exact tsub_le_iff_right.mpr
    (projected_cover_le_retained_area_add_shadow n T hT A E D V hcover hshadow)

theorem retained_area_pos_of_strict_shadow_bound
    {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (n : ℕ) (T : X → Y) (hT : LipschitzWith 1 T)
    (A E : Set X) (D V : Set Y)
    (hcover : D ⊆ T '' A) (hshadow : T '' (A \ E) ⊆ V)
    (hsmall : (μH[(n : ℝ)] : Measure Y) V < (μH[(n : ℝ)] : Measure Y) D) :
    0 < (μH[(n : ℝ)] : Measure X) (A ∩ E) := by
  have h := projected_cover_le_retained_area_add_shadow n T hT A E D V hcover hshadow
  by_contra hzero
  have hz : (μH[(n : ℝ)] : Measure X) (A ∩ E) = 0 := le_antisymm (not_lt.mp hzero) (zero_le)
  rw [hz, zero_add] at h
  exact (not_le.mpr hsmall) h

end

end RieszRectifiability

end OAI
