import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFineRoute
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridColor

namespace OAI

/-! Routing whole interactions retains constant congestion and the same color schedule. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaFineRouteSites {rows width A : ℕ} (p q : QMAFineGrid rows width A) :
    Finset (QMAFineGrid rows width A) := Finset.univ.image (qmaFineRoute p q)

theorem qmaFineRouteSites_local {rows width A : ℕ} (hA : 0 < A)
    (p q : QMAFineGrid rows width A) (a : QMAGridCell rows width)
    (hp : QMAGridCellsNear (qmaFineGridCell hA p) a)
    (hq : QMAGridCellsNear (qmaFineGridCell hA q) a)
    (z : QMAFineGrid rows width A) (hz : z ∈ qmaFineRouteSites p q) :
    QMAGridCellsNear (qmaFineGridCell hA z) a := by
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hz
  exact qmaFineRoute_local hA p q a hp hq k

theorem qmaFineRoutes_congestion {E : Type*} [Fintype E] {rows width A B : ℕ}
    (hA : 0 < A) (left right : E → QMAFineGrid rows width A)
    (anchor : E → QMAGridCell rows width)
    (hlocal : ∀ e, QMAGridCellsNear (qmaFineGridCell hA (left e)) (anchor e) ∧
      QMAGridCellsNear (qmaFineGridCell hA (right e)) (anchor e))
    (hdensity : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B)
    (z : QMAFineGrid rows width A) :
    (Finset.univ.filter (fun e => z ∈ qmaFineRouteSites (left e) (right e))).card ≤ 9*B := by
  apply qmaGrid_incidence_bound (qmaFineGridCell hA) anchor _ _ hdensity z
  intro e z hz
  exact qmaFineRouteSites_local hA _ _ _ (hlocal e).1 (hlocal e).2 z hz

theorem qmaFineRoutes_color_disjoint {E : Type*} [Fintype E] {rows width A B : ℕ}
    (hA : 0 < A) (left right : E → QMAFineGrid rows width A)
    (anchor : E → QMAGridCell rows width)
    (hlocal : ∀ e, QMAGridCellsNear (qmaFineGridCell hA (left e)) (anchor e) ∧
      QMAGridCellsNear (qmaFineGridCell hA (right e)) (anchor e))
    (hdensity : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B)
    {e f : E} (hef : e ≠ f) (hcolor : qmaGridColor anchor hdensity e = qmaGridColor anchor hdensity f) :
    Disjoint (qmaFineRouteSites (left e) (right e)) (qmaFineRouteSites (left f) (right f)) := by
  apply qmaGridColor_disjoint (qmaFineGridCell hA) anchor _ hdensity _ hef hcolor
  intro e z hz
  exact qmaFineRouteSites_local hA _ _ _ (hlocal e).1 (hlocal e).2 z hz

end ContinuumCoulomb

end

end OAI
