import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Map

namespace OAI

/-! Transfer a local image-measure identity through measurable coordinate
maps with an actual left inverse. No invariant-measure statement is assumed. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem measure_eq_of_map_eq_of_leftInverse_ae {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ₁ μ₂ : Measure X)
    (f : X → Y) (r : Y → X) (hf : Measurable f) (hr : Measurable r)
    (h₁ : ∀ᵐ x ∂μ₁, r (f x) = x) (h₂ : ∀ᵐ x ∂μ₂, r (f x) = x)
    (heq : Measure.map f μ₁ = Measure.map f μ₂) : μ₁ = μ₂ := by
  have hleft (μ : Measure X) (h : ∀ᵐ x ∂μ, r (f x) = x) :
      Measure.map r (Measure.map f μ) = μ := by
    rw [Measure.map_map hr hf]
    calc
      _ = Measure.map id μ := Measure.map_congr h
      _ = μ := Measure.map_id
  exact (hleft μ₁ h₁).symm.trans ((congrArg (Measure.map r) heq).trans (hleft μ₂ h₂))

theorem coordinate_map_restrict {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (C : ℝ≥0∞) (f : X → Y) (hf : Measurable f)
    (S : Set X) (T : Set Y) (hfi : InjOn f S) (hfT : MapsTo f S T)
    (hchart : Measure.map f (μ.restrict S) = C • ν.restrict T)
    (V : Set X) (hVS : V ⊆ S) (himage : MeasurableSet (f '' V)) :
    Measure.map f (μ.restrict V) = C • ν.restrict (f '' V) := by
  have hpre : f ⁻¹' (f '' V) ∩ S = V := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, heq⟩, hx⟩
      exact (hfi (hVS hy) hx heq) ▸ hy
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hVS hx⟩
  have hsub : f '' V ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfT (hVS hx)
  calc
    _ = (Measure.map f (μ.restrict S)).restrict (f '' V) := by
      rw [Measure.restrict_map hf himage, Measure.restrict_restrict (hf himage), hpre]
    _ = C • ν.restrict (f '' V) := by
      rw [hchart, Measure.restrict_smul, Measure.restrict_restrict himage,
        inter_eq_left.mpr hsub]

theorem local_image_measure_of_coordinates {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (C : ℝ≥0∞)
    (f : X → Y) (r : Y → X) (hf : Measurable f) (hr : Measurable r)
    (S : Set X) (T : Set Y) (hS : MeasurableSet S)
    (hleft : ∀ x ∈ S, r (f x) = x) (hfT : MapsTo f S T)
    (hchart : Measure.map f (μ.restrict S) = C • ν.restrict T)
    (Φ : X → X) (F : Y → Y) (hΦ : Measurable Φ) (hF : Measurable F)
    (U : Set X) (hU : MeasurableSet U) (hUS : U ⊆ S) (hΦS : Φ '' U ⊆ S)
    (hΦU : MeasurableSet (Φ '' U)) (hfU : MeasurableSet (f '' U))
    (hfΦU : MeasurableSet (f '' (Φ '' U)))
    (hconj : ∀ x ∈ U, f (Φ x) = F (f x))
    (hvolume : Measure.map F (ν.restrict (f '' U)) = ν.restrict (F '' (f '' U))) :
    Measure.map Φ (μ.restrict U) = μ.restrict (Φ '' U) := by
  have hfi : InjOn f S := by
    intro x hx y hy heq
    exact (hleft x hx).symm.trans ((congrArg r heq).trans (hleft y hy))
  have hu := coordinate_map_restrict μ ν C f hf S T hfi hfT hchart U hUS hfU
  have hw := coordinate_map_restrict μ ν C f hf S T hfi hfT hchart
    (Φ '' U) hΦS hfΦU
  have himage : F '' (f '' U) = f '' (Φ '' U) := by
    simp only [image_image]
    apply image_congr
    intro x hx
    exact (hconj x hx).symm
  have hpush : Measure.map f (Measure.map Φ (μ.restrict U)) =
      Measure.map f (μ.restrict (Φ '' U)) := by
    calc
      _ = Measure.map F (Measure.map f (μ.restrict U)) := by
        rw [Measure.map_map hf hΦ, Measure.map_map hF hf]
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem hU] with x hx
        exact hconj x hx
      _ = C • ν.restrict (f '' (Φ '' U)) := by
        rw [hu, Measure.map_smul _ hF.aemeasurable, hvolume, himage]
      _ = _ := hw.symm
  have hsupport : ∀ᵐ x ∂Measure.map Φ (μ.restrict U), x ∈ S := by
    apply (ae_map_iff hΦ.aemeasurable hS).mpr
    filter_upwards [ae_restrict_mem hU] with x hx
    exact hΦS ⟨x, hx, rfl⟩
  apply measure_eq_of_map_eq_of_leftInverse_ae _ _ f r hf hr _ _ hpush
  · filter_upwards [hsupport] with x hx
    exact hleft x hx
  · filter_upwards [ae_restrict_mem hΦU] with x hx
    exact hleft x (hΦS hx)

end
end PositiveEinsteinFour.Geometry

end OAI
