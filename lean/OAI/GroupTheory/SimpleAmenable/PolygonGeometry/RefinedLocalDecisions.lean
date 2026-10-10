import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.InactiveNeighborhoodActions
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FiniteRefiningGrid
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.LocalClippedBoxFormula

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RefinedLocalDecisions

theorem refinedGridRectangle_point_near {a N : ℕ} (e : Fin (N+1) → CutRing)
    (he : StrictMono (fun i => ordinary (e i))) (hzero : e 0=0) (hlast : e (Fin.last N)=1)
    (hmesh : ∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1)
    (cell : Fin 2 → Fin N) (z : ℝ × ℝ) (δ : ℝ)
    (hnear : ∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ)
    (p : GenericSquare a) (hp : p ∈ (refinedGridRectangle a N e cell).val) : dist p.val z<δ := by
  have hb := (refinedGridRectangle_mem e he hzero hlast hmesh cell p).mp hp
  have hd (k : Fin 2) : |realCoordinate p.val k-realCoordinate z k|<δ := by
    have hl := (abs_lt.mp (hnear k).1).1
    have hr := (abs_lt.mp (hnear k).2).2
    have hk := hb k
    change ordinary (e (cell k).castSucc)≤realCoordinate p.val k ∧
      realCoordinate p.val k<ordinary (e (cell k).succ) at hk
    rw [abs_lt]
    constructor <;> linarith [hk.1,hk.2]
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff]
  exact ⟨hd 0,hd 1⟩

namespace ConcurrentGeometry.InwardChart
variable {a : ℕ} {r : CutRing} {C : ConcurrentGeometry a r} {ι : Type*} [Finite ι]
    {j : ι → Fin 4} {c : ι → CutRing} {z : ℝ × ℝ} (T : C.InwardChart j c z)

theorem refined_cells_locally_decided (hr : 0<ordinary r ∧ ordinary r<1/2) :
    ∃ δ : ℝ, 0<δ ∧ ∀ (N : ℕ) (e : Fin (N+1) → CutRing),
    StrictMono (fun i => ordinary (e i)) → e 0=0 → e (Fin.last N)=1 →
    (∀ i : Fin N, ordinary (e i.succ)-ordinary (e i.castSucc)<1) →
    ∀ cell : Fin 2 → Fin N,
    (∀ k, |ordinary (e (cell k).castSucc)-realCoordinate z k|<δ ∧
      |ordinary (e (cell k).succ)-realCoordinate z k|<δ) →
    ∀ p : GenericSquare a, p ∈ (refinedGridRectangle a N e cell).val →
      p ∈ (C.inwardMargin T.vertex T.offset z).val ∧
      ∀ i, p ∈ (C.localDecision T.vertex T.offset z (j i) (c i)).val ↔
        p ∈ (cutPolygon a (j i) (c i)).val := by
  obtain ⟨O,hO,hz,hlocal⟩ := T.decisions_locally_eq hr
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hO z hz
  refine ⟨δ,hδ,?_⟩
  intro N e he hzero hlast hmesh cell hnear p hp
  exact hlocal p (hball (refinedGridRectangle_point_near e he hzero hlast hmesh cell z δ hnear p hp))

end ConcurrentGeometry.InwardChart
end RefinedLocalDecisions

end SimpleAmenable
end
end

end OAI
