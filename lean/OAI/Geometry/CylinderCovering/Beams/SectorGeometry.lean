import OAI.Geometry.CylinderCovering.Barycentric.Sector
import OAI.Geometry.CylinderCovering.Beams.Neighborhood
import OAI.Geometry.CylinderCovering.Beams.FullDefinitions
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering.BeamNeighborhood

lemma sector_eq_signedSector (a l r δ : ℝ) :
    sector a l r δ =
      RadialCoordinates.BarycentricSector.signedSector l r δ (2-a+δ) := rfl

theorem sector_eq_two_triangles {a l r δ : ℝ}
    (ha : a ≤ 2) (hlr : l ≤ r) (hδ : 0 ≤ δ) :
    sector a l r δ =
      convexHull ℝ (range (RadialCoordinates.BarycentricSector.vertices l r (2-a+δ))) ∪
      (fun z : Plane => -z) ''
        convexHull ℝ (range (RadialCoordinates.BarycentricSector.vertices l r δ)) := by
  rw [sector_eq_signedSector]
  exact RadialCoordinates.BarycentricSector.signedSector_eq_two_triangles
    hlr hδ (by linarith)

theorem sector_area {a l r δ : ℝ}
    (ha : a ≤ 2) (hlr : l ≤ r) (hδ : 0 ≤ δ) :
    volume.real (sector a l r δ) = ((2-a+δ)^2+δ^2)/2*(r-l) := by
  rw [sector_eq_signedSector,
    RadialCoordinates.BarycentricSector.signedSector_area hlr hδ (by linarith)]
  ring

theorem sector_perimeters_le {a l r δ : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 2) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    RadialCoordinates.BarycentricSector.perimeter l r δ +
      RadialCoordinates.BarycentricSector.perimeter l r (2-a+δ) ≤
        4*(2+Real.sqrt 2) := by
  have h₁ := RadialCoordinates.BarycentricSector.perimeter_le hl hlr hr hδ
  have h₂ := RadialCoordinates.BarycentricSector.perimeter_le hl hlr hr
    (show 0 ≤ 2-a+δ by linarith)
  have hs := Real.sqrt_nonneg (2:ℝ)
  have hm := mul_le_mul_of_nonneg_left (show 2-a+2*δ ≤ 4 by linarith)
    (show 0 ≤ 2+Real.sqrt 2 by positivity)
  nlinarith

theorem sector_area_error {a l r δ : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 2) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1)
    (hlen : r-l = δ) :
    0 ≤ volume.real (sector a l r δ) - (2-a)^2/2*δ ∧
    volume.real (sector a l r δ) - (2-a)^2/2*δ ≤ 3*δ^2 := by
  rw [sector_area ha' (by linarith) hδ, hlen]
  have hδ3 : δ^3 ≤ δ^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hδ' (sq_nonneg δ)]
  have hnonneg : 0 ≤ (2-a)*δ^2+δ^3 := by positivity
  have hbound : (2-a)*δ^2 ≤ 2*δ^2 := by nlinarith [sq_nonneg δ]
  constructor <;> nlinarith

end CylinderCovering.BeamNeighborhood

namespace ShortenedBeam
open CylinderCovering

lemma doubleSector_eq_signedSectorModel (a : ℝ) (N : ℕ) (i : Fin N) :
    doubleSector a N i = BeamNeighborhood.sector a
      (RadialRiemann.point 0 1 N i) (RadialRiemann.point 0 1 N (i+1)) (1/(N:ℝ)) := by
  have hv (d p : ℝ) : (!₂[d*p,d*(1-p)] : ParameterPlane) =
      d • (!₂[p,1-p] : ParameterPlane) := by
    ext j
    fin_cases j <;> rfl
  ext z
  simp only [doubleSector, BeamNeighborhood.sector, RadialRiemann.cell,
    BeamNeighborhood.radial, hv]

theorem doubleSector_area {a : ℝ} (ha : a ≤ 2)
    (N : ℕ) (i : Fin N) :
    volume.real (doubleSector a N i) =
      ((2-a+1/(N:ℝ))^2+(1/(N:ℝ))^2)/2*(1/(N:ℝ)) := by
  have hδ : 0 ≤ 1/(N:ℝ) := by positivity
  have hlen : RadialRiemann.point 0 1 N (i+1) - RadialRiemann.point 0 1 N i =
      1/(N:ℝ) := by
    rw [RadialRiemann.point_succ]
    simp [RadialRiemann.step]
  rw [doubleSector_eq_signedSectorModel, BeamNeighborhood.sector_area ha (by linarith) hδ, hlen]

end ShortenedBeam

end

end OAI
