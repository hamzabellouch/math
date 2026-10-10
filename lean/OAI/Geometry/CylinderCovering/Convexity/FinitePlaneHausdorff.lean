import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace CylinderCovering.FinitePlaneHausdorff

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

omit [InnerProductSpace ℝ E] in
theorem compact_subset_isometry_range_measure_lt_top
    {f : F → E} (hf : Isometry f) {S : Set E} (hS : IsCompact S)
    (hplane : S ⊆ range f) :
    Measure.euclideanHausdorffMeasure (Module.finrank ℝ F) S < ⊤ := by
  have hc : IsCompact (f ⁻¹' S) := hf.isClosedEmbedding.isCompact_preimage hS
  rw [← image_preimage_eq_of_subset hplane, hf.euclideanHausdorffMeasure_image,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact hc.measure_lt_top

variable [FiniteDimensional ℝ E]

theorem compact_subset_affine_plane_measure_lt_top
    (V : Submodule ℝ E) (p : E) {S : Set E} (hS : IsCompact S)
    (hplane : ∀ x ∈ S, x - p ∈ V) :
    Measure.euclideanHausdorffMeasure (Module.finrank ℝ V) S < ⊤ := by
  let f : V → E := fun y => p + (y : E)
  have hf : Isometry f := (isometry_add_left p).comp isometry_subtype_coe
  apply compact_subset_isometry_range_measure_lt_top hf hS
  intro x hx
  refine ⟨⟨x - p, hplane x hx⟩, ?_⟩
  change p + (x - p) = x
  abel

omit [MeasurableSpace E] [BorelSpace E] in
theorem orthogonal_unit_finrank {u : E} (hu : ‖u‖ = 1) :
    Module.finrank ℝ ((ℝ ∙ u)ᗮ) = Module.finrank ℝ E - 1 := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hr := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hu0] at hr
  omega

theorem compact_affine_hyperplane_measure_lt_top
    {u : E} (hu : ‖u‖ = 1) (c : ℝ) {S : Set E} (hS : IsCompact S)
    (hplane : ∀ x ∈ S, inner ℝ u x = c) :
    Measure.euclideanHausdorffMeasure (Module.finrank ℝ E - 1) S < ⊤ := by
  rw [← orthogonal_unit_finrank hu]
  apply compact_subset_affine_plane_measure_lt_top ((ℝ ∙ u)ᗮ) (c • u) hS
  intro x hx
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  simp [inner_sub_right, inner_smul_right, hplane x hx, hu]

theorem compact_perpendicular_measure_lt_top
    {u : E} (hu : ‖u‖ = 1) {S : Set E} (hS : IsCompact S)
    (hplane : ∀ x ∈ S, inner ℝ u x = 0) :
    Measure.euclideanHausdorffMeasure (Module.finrank ℝ E - 1) S < ⊤ :=
  compact_affine_hyperplane_measure_lt_top hu 0 hS hplane

end CylinderCovering.FinitePlaneHausdorff

end

end OAI
