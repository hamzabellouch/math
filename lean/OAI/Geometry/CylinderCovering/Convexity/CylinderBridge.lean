import OAI.Geometry.CylinderCovering.Convexity.CylinderBridgeDefinitions
import OAI.Geometry.TriangularCovering.Main
import OAI.Geometry.CylinderCovering.Convexity.OpenBaseApproximation

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace TriangularCovering

@[simp] theorem TriCylinder.toCylinder_axis (C : TriCylinder) :
    C.toCylinder.axis = C.axis := rfl

theorem TriCylinder.toCylinder_base_image (C : TriCylinder) :
    (Subtype.val : (normalPlane C.axis) → Space) '' C.toCylinder.base = C.base := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro hx
    have hp : x ∈ normalPlane C.axis :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (C.perpendicular x hx)
    exact ⟨⟨x, hp⟩, hx, rfl⟩

@[simp] theorem TriCylinder.toCylinder_carrier (C : TriCylinder) :
    C.toCylinder.carrier = C.carrier := by
  ext x
  constructor
  · rintro ⟨b, hb, t, ht⟩
    exact ⟨b, hb, t, ht⟩
  · rintro ⟨b, hb, t, ht⟩
    have hp : b ∈ normalPlane C.axis :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (C.perpendicular b hb)
    exact ⟨⟨b, hp⟩, hb, t, ht⟩

@[simp] theorem TriCylinder.toCylinder_area (C : TriCylinder) :
    C.toCylinder.area = area C.base := by
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure (normalPlane C.axis)) =
      volume := by
    simpa only [normalPlane_rank C.unit_axis] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := normalPlane C.axis))
  rw [← C.toCylinder_base_image]
  change volume.real {x : normalPlane C.axis | (x : Space) ∈ C.base} =
    (Measure.euclideanHausdorffMeasure 2
      ((Subtype.val : normalPlane C.axis → Space) ''
        {x : normalPlane C.axis | (x : Space) ∈ C.base})).toReal
  rw [isometry_subtype_coe.euclideanHausdorffMeasure_image, hm]
  rfl

theorem TriCylinder.toCylinder_compact (C : TriCylinder) :
    IsCompact C.toCylinder.base := by
  have himage := C.toCylinder_base_image
  exact Subtype.isCompact_iff.mpr (himage.symm ▸ C.compact)

end TriangularCovering

namespace RuledApproximation

theorem Cylinder.shadowArea_eq_global (C : Cylinder) (S : Set Space) :
    C.shadowArea S = CylinderCovering.shadowArea S C.axis := by
  let P := TriangularCovering.normalPlane C.axis
  have hp : Module.finrank ℝ P = 2 := TriangularCovering.normalPlane_rank C.unit_axis
  have hm : (Measure.euclideanHausdorffMeasure 2 : Measure P) = volume := by
    simpa only [hp] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := P))
  have himage : TriangularCovering.projection C.axis '' S =
      (Subtype.val : P → Space) '' (P.orthogonalProjectionOnto '' S) := by
    rw [image_image]
    congr 1
    funext z
    exact (TriangularCovering.normalPlane_projection C.unit_axis z).symm
  unfold Cylinder.shadowArea CylinderCovering.shadowArea TriangularCovering.area
  rw [himage, isometry_subtype_coe.euclideanHausdorffMeasure_image, hm]
  rfl

theorem familyRelativeArea_eq_global {n : ℕ} (C : Fin n → Cylinder) (S : Set Space) :
    familyRelativeArea C S = CylinderCovering.relativeCost S C := by
  simp only [familyRelativeArea, CylinderCovering.relativeCost, Cylinder.shadowArea_eq_global]

end RuledApproximation

namespace CylinderCovering

theorem openCounterexample_of_compact {S : Set Space} {n : ℕ}
    (C : Fin n → RuledApproximation.Cylinder)
    (hcompact : ∀ i, IsCompact (C i).base)
    (hcov : S ⊆ RuledApproximation.familySet C)
    (harea : RuledApproximation.familyArea C < minimumShadowArea S / 2)
    (hrelative : relativeCost S C < 1 / 2) :
    ∃ D : Fin n → RuledApproximation.Cylinder,
      (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openBounded) ∧ S ⊆ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea D < minimumShadowArea S / 2 ∧
      relativeCost S D < 1 / 2 := by
  rw [← RuledApproximation.familyRelativeArea_eq_global] at hrelative
  obtain ⟨D, haxis, hopen, hCD, hDarea, hDrelative⟩ :=
    RuledApproximation.family_enlarge_open_two_budgets C S hcompact harea hrelative
  rw [RuledApproximation.familyRelativeArea_eq_global] at hDrelative
  exact ⟨D, haxis, hopen, hcov.trans hCD, hDarea, hDrelative⟩

theorem openCounterexample_of_triangular {S : Set Space} {n : ℕ}
    (C : Fin n → TriangularCovering.TriCylinder)
    (hcov : triangularCovers S C)
    (harea : TriangularCovering.totalArea C < minimumShadowArea S / 2)
    (hrelative : triangularRelativeCost S C < 1 / 2) :
    ∃ D : Fin n → RuledApproximation.Cylinder,
      (∀ i, (D i).axis = (C i).axis) ∧
      (∀ i, (D i).openBounded) ∧ S ⊆ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea D < minimumShadowArea S / 2 ∧
      relativeCost S D < 1 / 2 := by
  let C' : Fin n → RuledApproximation.Cylinder := fun i => (C i).toCylinder
  have harea' : RuledApproximation.familyArea C' < minimumShadowArea S / 2 := by
    simpa only [RuledApproximation.familyArea, C',
      TriangularCovering.TriCylinder.toCylinder_area, TriangularCovering.totalArea] using harea
  have hrel' : RuledApproximation.familyRelativeArea C' S < 1 / 2 := by
    simpa only [RuledApproximation.familyRelativeArea, C',
      TriangularCovering.TriCylinder.toCylinder_area,
      RuledApproximation.Cylinder.shadowArea_eq_global,
      TriangularCovering.TriCylinder.toCylinder_axis, triangularRelativeCost] using hrelative
  obtain ⟨D, haxis, hopen, hCD, hDarea, hDrelative⟩ :=
    RuledApproximation.family_enlarge_open_two_budgets C' S
      (fun i => (C i).toCylinder_compact) harea' hrel'
  refine ⟨D, haxis, hopen, ?_, hDarea, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := hcov x hx
    apply hCD
    apply mem_iUnion.mpr
    exact ⟨i, by simpa only [C', TriangularCovering.TriCylinder.toCylinder_carrier] using hi⟩
  · rwa [RuledApproximation.familyRelativeArea_eq_global] at hDrelative

theorem regularOpen_of_regularTriangular
    (h : RegularTriangularCounterexampleStatement) : RegularOpenCounterexampleStatement := by
  intro S hS
  obtain ⟨n, C, hcov, harea, hrelative⟩ := h S hS
  obtain ⟨D, _, hopen, hcovD, hareaD, hrelativeD⟩ :=
    openCounterexample_of_triangular C hcov harea hrelative
  exact ⟨n, D, hopen, hcovD, hareaD, hrelativeD⟩

end CylinderCovering

end

end OAI
