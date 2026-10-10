import OAI.Geometry.CylinderCovering.Physical.PhysicalFootprintsDefinitions
import OAI.Geometry.RuledCovering.Main
import OAI.Geometry.CylinderCovering.Footprints.Shapes

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.PhysicalFootprints
open RuledApproximation

theorem footCoordinates_continuous : Continuous footCoordinates := by
  unfold footCoordinates vec2
  fun_prop

theorem footCoordinates_injective : Function.Injective footCoordinates := by
  intro p q hpq
  have h0 := congrArg (fun z : Plane => z 0) hpq
  have h1 := congrArg (fun z : Plane => z 1) hpq
  simp only [footCoordinates, vec2_apply_zero, vec2_apply_one] at h0 h1
  exact Prod.ext (by linarith) h0

def footCoordinatesLinear : (ℝ × ℝ) →ₗ[ℝ] Plane where
  toFun q := vec2 q.2 (-q.1)
  map_add' p q := by
    ext i
    fin_cases i <;> simp [vec2]
    ring
  map_smul' c q := by ext i; fin_cases i <;> simp [vec2]

def footCoordinatesAffine : (ℝ × ℝ) →ᵃ[ℝ] Plane where
  toFun := footCoordinates
  linear := footCoordinatesLinear
  map_vadd' p v := by
    ext i
    fin_cases i <;> simp [footCoordinates, footCoordinatesLinear, vec2]
    ring

def projectedFootAffine (h : ℝ) (g : Plane) : (ℝ × ℝ) →ᵃ[ℝ] Space :=
  (rawProjection h g).toAffineMap.comp footCoordinatesAffine

theorem projectedFootAffine_apply (h : ℝ) (g : Plane) (q : ℝ × ℝ) :
    projectedFootAffine h g q = projectedFoot h g q := rfl

def perpendicularFootAffine (h : ℝ) (g : Plane) :
    (ℝ × ℝ) →ᵃ[ℝ] ((Submodule.span ℝ ({physicalUnit h g} : Set Space))ᗮ) :=
  (perpendicularProjection h g).toAffineMap.comp footCoordinatesAffine

theorem perpendicularFootAffine_injective {h : ℝ} (hh : 0 < h) (g : Plane) :
    Function.Injective (perpendicularFootAffine h g) :=
  (perpendicularProjection_injective hh g).comp footCoordinates_injective

theorem footCoordinates_measurePreserving :
    MeasurePreserving footCoordinates volume volume := by
  have hr : MeasurePreserving (fun x : ℝ => 1 - x) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left volume (1 : ℝ)).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hp : MeasurePreserving (fun q : ℝ × ℝ => (q.2, 1 - q.1)) volume volume := by
    simpa only [Function.comp_def, Prod.map, Prod.swap, id_eq, Measure.volume_eq_prod] using
      ((MeasurePreserving.id (volume : Measure ℝ)).prod hr).comp
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)))
  change MeasurePreserving (fun q : ℝ × ℝ => vec2 q.2 (1 - q.1)) volume volume
  simpa only [Function.comp_def, pairPlaneEquiv_apply] using
    pairPlane_measurePreserving.comp hp

theorem footCoordinates_volume {F : Set (ℝ × ℝ)} (hF : IsCompact F) :
    volume (footCoordinates '' F) = volume F := by
  have hm := footCoordinates_measurePreserving.measure_preimage
    (hF.image footCoordinates_continuous).measurableSet.nullMeasurableSet
  rw [Set.preimage_image_eq _ footCoordinates_injective] at hm
  exact hm.symm

theorem footCoordinates_volume_real {F : Set (ℝ × ℝ)} (hF : IsCompact F) :
    volume.real (footCoordinates '' F) = volume.real F := by
  simp only [measureReal_def, footCoordinates_volume hF]

theorem projectedFoot_eq_rawProjection (h : ℝ) (g : Plane) (q : ℝ × ℝ) :
    projectedFoot h g q = rawProjection h g (footCoordinates q) := rfl

theorem projectedFoot_injective {h : ℝ} (hh : 0 < h) (g : Plane) :
    Function.Injective (projectedFoot h g) := by
  intro p q hpq
  apply footCoordinates_injective
  apply perpendicularProjection_injective hh g
  apply Subtype.ext
  exact hpq

def footprintCylinder (h : ℝ) (g : Plane) (F : Set (ℝ × ℝ)) : Cylinder :=
  projectedCylinder h g (footCoordinates '' F)

theorem footprintCylinder_axis (h : ℝ) (g : Plane) (F : Set (ℝ × ℝ)) :
    (footprintCylinder h g F).axis = unitDirection h g := rfl

theorem footprintCylinder_base (h : ℝ) (g : Plane) (F : Set (ℝ × ℝ)) :
    Subtype.val '' (footprintCylinder h g F).base = projectedFoot h g '' F := by
  change Subtype.val '' (perpendicularProjection h g '' (footCoordinates '' F)) = _
  rw [Set.image_image, Set.image_image]
  rfl

theorem footprintCylinder_base_image (h : ℝ) (g : Plane) (F : Set (ℝ × ℝ)) :
    (footprintCylinder h g F).base = perpendicularFootAffine h g '' F := by
  change perpendicularProjection h g '' (footCoordinates '' F) = _
  rw [Set.image_image]
  rfl

theorem footprintCylinder_compact (h : ℝ) (g : Plane) {F : Set (ℝ × ℝ)}
    (hF : IsCompact F) : IsCompact (footprintCylinder h g F).base :=
  (hF.image footCoordinates_continuous).image
    (perpendicularProjection h g).continuous_of_finiteDimensional

theorem footprintCylinder_carrier (h : ℝ) (g : Plane) (F : Set (ℝ × ℝ)) :
    (footprintCylinder h g F).carrier = sweptFootprint h g F := by
  ext x
  rw [footprintCylinder, projectedCylinder_mem_iff]
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, s, hx⟩
    exact ⟨q, hq, s, hx⟩
  · rintro ⟨q, hq, s, hx⟩
    exact ⟨footCoordinates q, ⟨q, hq, rfl⟩, s, hx⟩

theorem footprintCylinder_area {h : ℝ} (hh : 0 < h) (g : Plane)
    {F : Set (ℝ × ℝ)} (hF : IsCompact F) :
    (footprintCylinder h g F).area = h * volume.real F * physicalWeight h g := by
  rw [footprintCylinder, projectedCylinder_area hh, footCoordinates_volume_real hF]

theorem physical_footprints : PhysicalStatement := by
  intro h g F hh hF
  have hcompact := footprintCylinder_compact h g hF
  exact ⟨projectedFoot_injective hh g, footprintCylinder h g F,
    footprintCylinder_axis h g F, footprintCylinder_base h g F,
    hcompact, hcompact.measurableSet, hcompact.measure_lt_top,
    footprintCylinder_carrier h g F, footprintCylinder_area hh g hF⟩

theorem projectedFoot_convex_iff {h : ℝ} (hh : 0 < h) (g : Plane)
    (F : Set (ℝ × ℝ)) : Convex ℝ (projectedFoot h g '' F) ↔ Convex ℝ F := by
  constructor
  · intro hconv
    have hp := hconv.affine_preimage (projectedFootAffine h g)
    change Convex ℝ (projectedFoot h g ⁻¹' (projectedFoot h g '' F)) at hp
    rwa [Set.preimage_image_eq _ (projectedFoot_injective hh g)] at hp
  · intro hconv
    exact hconv.affine_image (projectedFootAffine h g)

theorem projectedFoot_affineIndependent_iff {h : ℝ} (hh : 0 < h) (g : Plane)
    {ι : Type*} (p : ι → ℝ × ℝ) :
    AffineIndependent ℝ (projectedFoot h g ∘ p) ↔ AffineIndependent ℝ p :=
  (projectedFootAffine h g).affineIndependent_iff (projectedFoot_injective hh g)

theorem projectedFoot_convexHull (h : ℝ) (g : Plane) (F : Set (ℝ × ℝ)) :
    projectedFoot h g '' convexHull ℝ F = convexHull ℝ (projectedFoot h g '' F) :=
  (projectedFootAffine h g).image_convexHull F

theorem projection_shapes : ProjectionShapeStatement := by
  intro h g hh
  exact ⟨projectedFoot_convex_iff hh g,
    fun _ p => projectedFoot_affineIndependent_iff hh g p,
    projectedFoot_convexHull h g⟩

theorem footprintCylinder_triangle {h m M d A : ℝ} (hh : 0 < h) (g : Plane)
    (hd : 0 < d) (hlength : 0 < M + 2 * A * d) :
    (footprintCylinder h g (Footprints.affineFootprint m M d A (A / 2))).base =
      convexHull ℝ (range (perpendicularFootAffine h g ∘
        RadialTriangle.vertices (-A * d) (M + A * d) m d)) ∧
    AffineIndependent ℝ (perpendicularFootAffine h g ∘
      RadialTriangle.vertices (-A * d) (M + A * d) m d) := by
  constructor
  · rw [footprintCylinder_base_image, Footprints.affineFootprint_half_eq_convexHull hd hlength,
      (perpendicularFootAffine h g).image_convexHull, ← range_comp]
  · exact (Footprints.affineFootprint_half_vertices_independent hd hlength).map'
      (perpendicularFootAffine h g) (perpendicularFootAffine_injective hh g)

theorem footprintCylinder_trapezoid {h m M d A B : ℝ} (hh : 0 < h) (g : Plane)
    (hd : 0 < d) (hB : A / 2 < B) (hlength : 0 < M + 2 * A * d) :
    (footprintCylinder h g (Footprints.affineFootprint m M d A B)).base =
      convexHull ℝ (range (perpendicularFootAffine h g ∘
        Footprints.trapezoidVertices m M d A B)) ∧
    Function.Injective (perpendicularFootAffine h g ∘
      Footprints.trapezoidVertices m M d A B) := by
  constructor
  · rw [footprintCylinder_base_image]
    exact Footprints.affineFootprint_image_eq_convexHull (perpendicularFootAffine h g)
      hd hB hlength
  · exact Footprints.trapezoid_image_vertices_injective (perpendicularFootAffine h g)
      (perpendicularFootAffine_injective hh g) hd hB hlength

theorem footprintCylinder_convex_iff {h : ℝ} (hh : 0 < h) (g : Plane)
    (F : Set (ℝ × ℝ)) :
    Convex ℝ (footprintCylinder h g F).base ↔ Convex ℝ F := by
  rw [footprintCylinder_base_image]
  constructor
  · intro hconv
    have hp := hconv.affine_preimage (perpendicularFootAffine h g)
    rwa [Set.preimage_image_eq _ (perpendicularFootAffine_injective hh g)] at hp
  · exact fun hconv => hconv.affine_image (perpendicularFootAffine h g)

end CylinderCovering.PhysicalFootprints

end

end OAI
