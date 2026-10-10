import OAI.Analysis.Triangular.Signs.SineGrid0
import OAI.Analysis.Triangular.Signs.SineGrid1
import OAI.Analysis.Triangular.Signs.SineGrid2

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cell_geometry (u : Fin 30) (k : Fin 100) :
    0≤cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
    (∀ j : Fin 15,j≠localPivot u → 0≤cellSeparation u k j ∧ cellSeparation u k j≤18) := by
  fin_cases u
  · exact cellGeometry00 k
  · exact cellGeometry01 k
  · exact cellGeometry02 k
  · exact cellGeometry03 k
  · exact cellGeometry04 k
  · exact cellGeometry05 k
  · exact cellGeometry06 k
  · exact cellGeometry07 k
  · exact cellGeometry08 k
  · exact cellGeometry09 k
  · exact cellGeometry10 k
  · exact cellGeometry11 k
  · exact cellGeometry12 k
  · exact cellGeometry13 k
  · exact cellGeometry14 k
  · exact cellGeometry15 k
  · exact cellGeometry16 k
  · exact cellGeometry17 k
  · exact cellGeometry18 k
  · exact cellGeometry19 k
  · exact cellGeometry20 k
  · exact cellGeometry21 k
  · exact cellGeometry22 k
  · exact cellGeometry23 k
  · exact cellGeometry24 k
  · exact cellGeometry25 k
  · exact cellGeometry26 k
  · exact cellGeometry27 k
  · exact cellGeometry28 k
  · exact cellGeometry29 k
lemma cell_factors (u : Fin 30) (k : Fin 100) :
    (∀ j : Fin 15,0≤cellFactor u k j) ∧ cellBarrier u < ∏ j : Fin 15,(cellFactor u k j)^2 := by
  fin_cases u
  · exact cellFactors00 k
  · exact cellFactors01 k
  · exact cellFactors02 k
  · exact cellFactors03 k
  · exact cellFactors04 k
  · exact cellFactors05 k
  · exact cellFactors06 k
  · exact cellFactors07 k
  · exact cellFactors08 k
  · exact cellFactors09 k
  · exact cellFactors10 k
  · exact cellFactors11 k
  · exact cellFactors12 k
  · exact cellFactors13 k
  · exact cellFactors14 k
  · exact cellFactors15 k
  · exact cellFactors16 k
  · exact cellFactors17 k
  · exact cellFactors18 k
  · exact cellFactors19 k
  · exact cellFactors20 k
  · exact cellFactors21 k
  · exact cellFactors22 k
  · exact cellFactors23 k
  · exact cellFactors24 k
  · exact cellFactors25 k
  · exact cellFactors26 k
  · exact cellFactors27 k
  · exact cellFactors28 k
  · exact cellFactors29 k
end AtomicTriangular.Construction
end

end OAI
