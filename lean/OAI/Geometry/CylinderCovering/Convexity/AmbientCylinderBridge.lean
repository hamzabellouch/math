import OAI.Geometry.CylinderCovering.Convexity.AmbientCylinderDefinitions
import OAI.Geometry.CylinderCovering.Convexity.CylinderBridge

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace RuledApproximation

variable (u : Space) (hu : ‖u‖ = 1) (B : Set Space)

@[simp] theorem Cylinder.fromAmbientBase_axis :
    (Cylinder.fromAmbientBase u hu B).axis = u := rfl

theorem Cylinder.fromAmbientBase_image
    (hB : ∀ b ∈ B, ⟪u, b⟫_ℝ = 0) :
    (Subtype.val : ((Submodule.span ℝ ({u} : Set Space))ᗮ) → Space) ''
      (Cylinder.fromAmbientBase u hu B).base = B := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hx
    have hp : x ∈ (Submodule.span ℝ ({u} : Set Space))ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hB x hx)
    exact ⟨⟨x, hp⟩, hx, rfl⟩

theorem Cylinder.fromAmbientBase_carrier
    (hB : ∀ b ∈ B, ⟪u, b⟫_ℝ = 0) :
    (Cylinder.fromAmbientBase u hu B).carrier =
      {x | ∃ b ∈ B, ∃ t : ℝ, x = b + t • u} := by
  ext x
  constructor
  · rintro ⟨b, hb, t, ht⟩
    exact ⟨b, hb, t, ht⟩
  · rintro ⟨b, hb, t, ht⟩
    have hp : b ∈ (Submodule.span ℝ ({u} : Set Space))ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hB b hb)
    exact ⟨⟨b, hp⟩, hb, t, ht⟩

theorem Cylinder.fromAmbientBase_area
    (hB : ∀ b ∈ B, ⟪u, b⟫_ℝ = 0) :
    (Cylinder.fromAmbientBase u hu B).area = TriangularCovering.area B := by
  have hm : (Measure.euclideanHausdorffMeasure 2 :
      Measure ((Submodule.span ℝ ({u} : Set Space))ᗮ)) = volume := by
    change (Measure.euclideanHausdorffMeasure 2 :
      Measure (TriangularCovering.normalPlane u)) = volume
    simpa only [TriangularCovering.normalPlane_rank hu] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume
        (V := TriangularCovering.normalPlane u))
  conv_rhs => rw [← Cylinder.fromAmbientBase_image u hu B hB]
  change volume.real {x : (Submodule.span ℝ ({u} : Set Space))ᗮ | (x : Space) ∈ B} =
    (Measure.euclideanHausdorffMeasure 2
      ((Subtype.val : (Submodule.span ℝ ({u} : Set Space))ᗮ → Space) ''
        {x : (Submodule.span ℝ ({u} : Set Space))ᗮ | (x : Space) ∈ B})).toReal
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image, hm]
  rfl

theorem Cylinder.fromAmbientBase_compact
    (hB : ∀ b ∈ B, ⟪u, b⟫_ℝ = 0) (hcompact : IsCompact B) :
    IsCompact (Cylinder.fromAmbientBase u hu B).base := by
  exact Subtype.isCompact_iff.mpr
    ((Cylinder.fromAmbientBase_image u hu B hB).symm ▸ hcompact)

end RuledApproximation

end

end OAI
