import OAI.Geometry.CylinderCovering.Angular.GeneralGeometry
import OAI.Geometry.CylinderCovering.Radial.SectorEuclidean

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.AngularGeneral

lemma planarSector_eq_euclideanRadialSector (D : Data) (j : ℕ) :
    planarSector D j = AngularCaps.euclideanRadialSector
      (D.node j) (D.node (j+1)) (D.radius j) := by
  ext p
  exact (AngularCaps.mem_euclideanRadialSector).symm

lemma planarSector_volume {D : Data} {j : ℕ}
    (hnode : D.node j ≤ D.node (j+1))
    (hc : ContinuousOn (D.radius j) (interval D j))
    (hn : ∀ q ∈ interval D j, 0 ≤ D.radius j q) :
    volume.real (planarSector D j) =
      ∫ q in D.node j..D.node (j+1), (D.radius j q)^2 / 2 := by
  rw [planarSector_eq_euclideanRadialSector]
  exact AngularCaps.euclideanRadialSector_area hnode hc hn

theorem totalArea_div_H_eq_integralCost {τ η E : ℝ} {D : Data}
    (hD : Admissible τ η E D) :
    totalArea τ D / TriangularCovering.H = integralCost τ D := by
  apply integral_cost_of_planar_volumes
  intro j hj
  exact planarSector_volume (hD.2.2.2.1 j hj).le
    (hD.2.2.2.2.2.2.1 j hj)
    (fun q hq => (hD.2.2.2.2.2.2.2.1 j hj q hq).le)

end CylinderCovering.AngularGeneral

end

end OAI
