import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialExchange
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteCongestion

namespace OAI

/-! Explicit constant-length routes for the actual bounded-density exchange model. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def routeLeft (e : M.Term) : QMAFineGrid M.rows M.width A := M.qubitSlots.site (M.left e)
def routeRight (e : M.Term) : QMAFineGrid M.rows M.width A := M.qubitSlots.site (M.right e)
def routeLength (e : M.Term) : ℕ := qmaManhattanLength (qmaFineGridNat (M.routeLeft e)) (qmaFineGridNat (M.routeRight e))
def routeSites (e : M.Term) : Finset (QMAFineGrid M.rows M.width A) := qmaFineRouteSites (M.routeLeft e) (M.routeRight e)

theorem routeLength_bound (e : M.Term) : M.routeLength e ≤ 3*A+2 :=
  M.qubitSlots.route_length _ _ (M.anchor e) (M.geometry e).1 (M.geometry e).2

theorem route_local (hA : 0 < A) (e : M.Term) :
    QMAGridCellsNear (qmaFineGridCell hA (M.routeLeft e)) (M.anchor e) ∧
    QMAGridCellsNear (qmaFineGridCell hA (M.routeRight e)) (M.anchor e) := by
  simpa only [routeLeft,routeRight,QMACellSlots.site_cell] using M.geometry e

theorem route_congestion (hA : 0 < A) (z : QMAFineGrid M.rows M.width A) :
    (Finset.univ.filter (fun e => z ∈ M.routeSites e)).card ≤ 9*B :=
  qmaFineRoutes_congestion hA M.routeLeft M.routeRight M.anchor (M.route_local hA) M.termDensity z

theorem routes_of_color_disjoint (hA : 0 < A) {e f : M.Term} (hef : e ≠ f)
    (hcolor : M.termSlots.color e = M.termSlots.color f) :
    Disjoint (M.routeSites e) (M.routeSites f) :=
  by
    apply M.termSlots.color_disjoint (qmaFineGridCell hA) M.routeSites _ hef hcolor
    intro e z hz
    exact qmaFineRouteSites_local hA _ _ _ (M.route_local hA e).1 (M.route_local hA e).2 z hz

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
