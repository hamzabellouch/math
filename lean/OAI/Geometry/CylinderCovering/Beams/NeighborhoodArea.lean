import OAI.Geometry.CylinderCovering.Beams.NeighborhoodRealizationDefinitions
import OAI.Geometry.CylinderCovering.Beams.NeighborhoodEnclosure
import OAI.Geometry.CylinderCovering.Radial.Projection
import OAI.Geometry.CylinderCovering.Radial.ActualSweep
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace CylinderCovering.BeamNeighborhoodRealization
open RadialSweep

lemma physicalMap_continuous (D : Data) : Continuous (physicalMap D) := by
  unfold physicalMap
  fun_prop

lemma rawBase_compact (D : Data) (a l r δ : ℝ) : IsCompact (rawBase D a l r δ) :=
  (BeamNeighborhood.paddedSector_isCompact a l r δ).image (physicalMap_continuous D)

lemma base_compact (D : Data) (a l r δ : ℝ) : IsCompact (base D a l r δ) :=
  (rawBase_compact D a l r δ).image
    (TriangularCovering.projLinear (direction D ((l+r)/2))).continuous_of_finiteDimensional

lemma base_perpendicular (D : Data) (a l r δ : ℝ)
    (hu : ‖direction D ((l+r)/2)‖ = 1) :
    ∀ z ∈ base D a l r δ, inner ℝ (direction D ((l+r)/2)) z = 0 := by
  rintro z ⟨x,hx,rfl⟩
  exact TriangularCovering.projection_perp hu x

lemma base_covers_raw (D : Data) (a l r δ : ℝ) :
    rawBase D a l r δ ⊆ cylinder (direction D ((l+r)/2)) (base D a l r δ) :=
  _root_.OAI.RadialActualSweep.subset_projected_cylinder _ _

lemma base_area_le_of_enclosure (D : Data) {a l r δ L R : ℝ}
    (hδ : 0 < δ) (hLR : L < R)
    (hm : (l+r)/2 ∈ Icc D.α D.β)
    (hencl : ∀ z ∈ BeamNeighborhood.paddedSector a l r δ,
      (z 0+z 1,z 0) ∈ RadialTriangle.region L R ((l+r)/2) δ) :
    Measure.euclideanHausdorffMeasure 2 (base D a l r δ) ≠ ⊤ ∧
    TriangularCovering.area (base D a l r δ) ≤
      kappa D * δ * (R-L)^2 / (2*Real.sqrt (1+‖D.w ((l+r)/2)‖^2)) := by
  let T := RadialProjection.coordinateAffine D.p₀ D.a D.b ''
    RadialTriangle.region L R ((l+r)/2) δ
  have hraw : rawBase D a l r δ ⊆ T := by
    rintro z ⟨p,hp,rfl⟩
    exact ⟨(p 0+p 1,p 0),hencl p hp,rfl⟩
  have hT := RadialProjection.coordinate_region_image D.p₀ D.a D.b hLR hδ
    (m := (l+r)/2)
  have hdir : direction D ((l+r)/2) =
      TriangularCovering.unit (D.e+D.w ((l+r)/2)) := rfl
  have hnorm : ‖direction D ((l+r)/2)‖ = 1 := by
    rw [hdir]
    exact TriangularCovering.unit_norm
      (RadialProjection.sideways_ne_zero D.normal_unit (D.velocity_perp _ hm))
  have hf : Measure.euclideanHausdorffMeasure 2
      (TriangularCovering.projection (direction D ((l+r)/2)) '' T) ≠ ⊤ := by
    dsimp [T]
    rw [hT,TriangularCovering.projection_triangle_measure hnorm]
    exact ENNReal.ofReal_ne_top
  have hproj : base D a l r δ ⊆
      TriangularCovering.projection (direction D ((l+r)/2)) '' T := image_mono hraw
  refine ⟨ne_top_of_le_ne_top hf (measure_mono hproj),?_⟩
  calc
    _ ≤ TriangularCovering.area
        (TriangularCovering.projection (direction D ((l+r)/2)) '' T) :=
      ENNReal.toReal_mono hf (measure_mono hproj)
    _ = _ := by
      dsimp [T]
      rw [hT,hdir]
      exact RadialProjection.collar_projection_area D.p₀ D.e D.a D.b
        (D.w ((l+r)/2)) L R ((l+r)/2) δ D.normal_unit D.a_perp D.b_perp
        (D.velocity_perp _ hm) hδ.le

lemma padded_coordinates {a l r δ : ℝ}
    (_ : 0 ≤ a) (_ : a ≤ 1/2) (hl : 0 ≤ l) (hr : r ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlen : r-l = δ) :
    ∀ z ∈ BeamNeighborhood.paddedSector a l r δ,
      (z 0+z 1,z 0) ∈ RadialTriangle.region (-10*δ) (2-a+δ+2*δ^2)
        ((l+r)/2) δ := by
  intro z hz
  change z ∈ Metric.cthickening (δ^2) (BeamNeighborhood.sector a l r δ) at hz
  rw [(BeamNeighborhood.sector_isCompact a l r δ).cthickening_eq_biUnion_closedBall (sq_nonneg δ)] at hz
  simp only [mem_iUnion, Metric.mem_closedBall] at hz
  obtain ⟨q, ⟨p,hp,d,hd,rfl⟩, hdist⟩ := hz
  rw [dist_eq_norm] at hdist
  let x := z 0-d*p
  let y := z 1-d*(1-p)
  have hx : |x| ≤ δ^2 := by
    have h := (PiLp.norm_apply_le (z-d • BeamNeighborhood.radial p) 0).trans hdist
    simpa [x,BeamNeighborhood.radial,Real.norm_eq_abs] using h
  have hy : |y| ≤ δ^2 := by
    have h := (PiLp.norm_apply_le (z-d • BeamNeighborhood.radial p) 1).trans hdist
    simpa [y,BeamNeighborhood.radial,Real.norm_eq_abs] using h
  have hb := BeamNeighborhood.noisy_sector_bounds hl hr hδ.le hδ1 hlen hp hd hx hy
  have hsum : d+x+y = z 0+z 1 := by dsimp [x,y]; ring
  have hfirst : d*p+x = z 0 := by dsimp [x]; ring
  rw [hsum,hfirst] at hb
  have hδ2 : δ^2 ≤ δ := by nlinarith
  refine ⟨?_,hb.2.1,?_⟩
  · nlinarith only [hb.1,hδ2,hδ]
  · change |z 0-((l+r)/2)*(z 0+z 1)| ≤ δ/2*(z 0+z 1-(-10*δ))
    nlinarith only [hb.2.2]

lemma base_area_le (D : Data) {a l r δ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/2) (hl : 0 ≤ l) (hr : r ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlen : r-l = δ)
    (hm : (l+r)/2 ∈ Icc D.α D.β) :
    Measure.euclideanHausdorffMeasure 2 (base D a l r δ) ≠ ⊤ ∧
    TriangularCovering.area (base D a l r δ) ≤
      kappa D*δ*(2-a+11*δ+2*δ^2)^2/(2*Real.sqrt (1+‖D.w ((l+r)/2)‖^2)) := by
  have hLR : -10*δ < 2-a+δ+2*δ^2 := by nlinarith [sq_nonneg δ]
  have hh := base_area_le_of_enclosure D hδ hLR hm
    (padded_coordinates ha ha1 hl hr hδ hδ1 hlen)
  simpa only [show 2-a+δ+2*δ^2-(-10*δ) = 2-a+11*δ+2*δ^2 by ring] using hh

end CylinderCovering.BeamNeighborhoodRealization

end

end OAI
