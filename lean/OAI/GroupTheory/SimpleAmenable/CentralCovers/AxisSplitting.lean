import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CellGeometry
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteSectorPartition

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section AxisSplitting
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem axisSector_split (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u v w : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hlen : ordinary w-ordinary u < 1)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (s : TrackStar (Fin (m+1))) :
    B.axisSector hlarge n g d k hk p (coordinateInterval a d u w) s =
      B.axisSector hlarge n g d k hk p (coordinateInterval a d u v) s *
      B.axisSector hlarge n g d k hk p (coordinateInterval a d v w) s := by
  rw [coordinateInterval_union d u v w huv hvw hlen]
  exact B.fullGeometricSector_union hlarge _ _ _ _ (axisInterval_resolved d k p u v hu hv)
    (coordinateInterval_disjoint d u v v w huv le_rfl hvw hlen) s

theorem axisSector_split_commute (hlarge : 15 < m+1) (n : ℕ) (g : B.CoordinateWindowLaw n)
    (d : Fin 2) (k : ℕ) (hk : k ≤ n) (p : ℤ) (u v w : CutRing)
    (huv : ordinary u ≤ ordinary v) (hvw : ordinary v ≤ ordinary w)
    (hlen : ordinary w-ordinary u < 1)
    (hu : p ≤ endpointLabel u ∧ endpointLabel u < p+k)
    (hv : p ≤ endpointLabel v ∧ endpointLabel v < p+k)
    (s t : TrackStar (Fin (m+1))) :
    Commute (B.axisSector hlarge n g d k hk p (coordinateInterval a d u v) s)
      (B.axisSector hlarge n g d k hk p (coordinateInterval a d v w) t) :=
  B.fullGeometricSector_commute hlarge _ _ _ _ (axisInterval_resolved d k p u v hu hv)
    (coordinateInterval_disjoint d u v v w huv le_rfl hvw hlen) s t

end InitialCoverSystem
end AxisSplitting

end SimpleAmenable
end
end

end OAI
