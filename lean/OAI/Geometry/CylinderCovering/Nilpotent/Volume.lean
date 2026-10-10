import OAI.Geometry.CylinderCovering.Nilpotent.Similarity
import OAI.Geometry.CylinderCovering.Rational.TetrahedronVolume
import OAI.Geometry.CylinderCovering.Convexity.TetrahedronIdentification
import OAI.Geometry.CylinderCovering.Simplex.Diameter

namespace OAI

open MeasureTheory RuledApproximation

noncomputable section
namespace CylinderCovering.Nilpotent

theorem tetrahedron_volume :
    volume.real tetrahedron = 2 * Real.sqrt 2 / 3 := by
  have hscale := centerMap_volume tetrahedron
  rw [centerMap_tetrahedron, SlopeRational.referenceTetrahedron_volume] at hscale
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  change (1 / Real.sqrt 2) / 6 = volume.real tetrahedron / 8 at hscale
  have hidentity : (1 / Real.sqrt 2) / 6 = Real.sqrt 2 / 12 := by
    field_simp [hspos.ne']
    nlinarith [hsq]
  rw [hidentity] at hscale
  linarith

theorem tetrahedron_diameter : Metric.diam tetrahedron = 2 := by
  rw [ruled_tetrahedron_eq_triangular, TriangularCovering.K_eq_convexHull]
  exact SimplexDiameter.regular_convexHull_diameter
    TriangularCovering.tetraVertices (by norm_num)
    (fun _ _ hij => TriangularCovering.tetra_edge_length hij)

end CylinderCovering.Nilpotent

end

end OAI
