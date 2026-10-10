import OAI.MeasureTheory.Falconer.Slicing.PlanarSliceGeometry
import OAI.MeasureTheory.Falconer.Slicing.SliceTubeGeometry

namespace OAI

/-! # Isometric slice coordinates aligned with the center of a direction chart -/

namespace Falconer
open NormedSpace
variable {d m : ℕ}

theorem slice_isometry_normalize (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (x : V) : e (normalize x) = normalize (e x) := by
  simp only [NormedSpace.normalize,map_smul,e.norm_map]

theorem slice_isometry_perpendicular (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) (w x : V) :
    e (perpendicularPart w x) = perpendicularPart (e w) (e x) := by
  simp only [perpendicularPart,map_sub,map_smul,e.inner_map_map]

theorem exists_oriented_slice_coordinates (V : Submodule ℝ (Space d))
    (hm : Module.finrank ℝ V = m) (hmpos : 0 < m) (w₀ : Space d)
    (hw₀ : V.starProjection w₀ ≠ 0) :
    ∃ e : V ≃ₗᵢ[ℝ] Space m,
      normalize (e (V.orthogonalProjectionOnto w₀)) =
        EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hmpos⟩ := by
  let e₀ := sliceCoordinates V hm
  have hv : e₀ (V.orthogonalProjectionOnto w₀) ≠ 0 := by
    intro hzero
    have hp : V.orthogonalProjectionOnto w₀ = 0 := e₀.injective (by simpa using hzero)
    exact hw₀ (congrArg Subtype.val hp)
  obtain ⟨R,hR⟩ := exists_unit_axis_isometry hmpos (norm_normalize hv)
  refine ⟨e₀.trans R,?_⟩
  change normalize (R (e₀ (V.orthogonalProjectionOnto w₀))) = _
  have hRN (v : Space m) : R (normalize v) = normalize (R v) := by
    simp only [NormedSpace.normalize,map_smul,R.norm_map]
  rw [← hRN]
  exact hR

theorem oriented_slice_direction_distance (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) {w w₀ : Sphere d} {δ δ₀ ρ : ℝ}
    (hδ : δ < 1) (hδ₀ : δ₀ < 1)
    (hw : w ∈ directionSliceBand V δ) (hw₀ : w₀ ∈ directionSliceBand V δ₀)
    (hclose : dist (w:Space d) (w₀:Space d) ≤ ρ) :
    dist (normalize (e (V.orthogonalProjectionOnto (w:Space d))))
      (normalize (e (V.orthogonalProjectionOnto (w₀:Space d)))) ≤ 2*δ+ρ+2*δ₀ := by
  rw [← slice_isometry_normalize V e,← slice_isometry_normalize V e,e.dist_map,dist_eq_norm]
  change ‖normalize (V.starProjection (w:Space d))-
    normalize (V.starProjection (w₀:Space d))‖ ≤ _
  calc
    _ ≤ ‖normalize (V.starProjection (w:Space d))-(w:Space d)‖+
        ‖(w:Space d)-normalize (V.starProjection (w₀:Space d))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*δ+(‖(w:Space d)-(w₀:Space d)‖+
        ‖(w₀:Space d)-normalize (V.starProjection (w₀:Space d))‖) :=
      add_le_add (directionSliceBand_normalize_error V hδ hw)
        (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ 2*δ+(ρ+2*δ₀) := add_le_add le_rfl
      (add_le_add hclose (by simpa only [norm_sub_rev] using
        directionSliceBand_normalize_error V hδ₀ hw₀))
    _ = _ := by ring

theorem oriented_slice_tube_width (V : Submodule ℝ (Space d))
    (e : V ≃ₗᵢ[ℝ] Space m) {w : Sphere d} {δ : ℝ}
    (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) (x a : Space d) :
    ‖perpendicularPart (normalize (e (V.orthogonalProjectionOnto (w:Space d))))
      (e (V.orthogonalProjectionOnto x)-e (V.orthogonalProjectionOnto a))‖ ≤
      ‖perpendicularPart (w:Space d) (x-a)‖ := by
  rw [← slice_isometry_normalize V e,← map_sub,← slice_isometry_perpendicular V e,e.norm_map]
  exact slice_projected_tube_width V hδ hw x a

end Falconer

end OAI
