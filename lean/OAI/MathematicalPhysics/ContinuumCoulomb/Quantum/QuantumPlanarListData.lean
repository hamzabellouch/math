import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPlanarRouteData
import Mathlib.Data.List.GetD

namespace OAI

/-! Convert the concrete finite cell paths to the coordinate-array interface used
by the fixed-round physical subdivision theorem. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

structure QMAPlanarListData (G : QMARationalExchangeGraph) where
  position : Fin G.n → ℕ × ℕ
  position_injective : Function.Injective position
  path : G.Edge → List (ℕ × ℕ)
  length : ∀ e, 3 ≤ (path e).length
  first : ∀ e, (path e).head? = some (position (G.left e))
  last : ∀ e, (path e).getLast? = some (position (G.right e))
  simple : ∀ e, (path e).Nodup
  step : ∀ e, (path e).IsChain (fun p q => qmaSquareGrid.Adj p q)
  positive : ∀ e p, p ∈ path e → 0 < p.1 ∧ 0 < p.2
  avoids : ∀ e v, position v ∉ ((path e).drop 1).dropLast
  disjoint : ∀ e f, e ≠ f →
    Disjoint (((path e).drop 1).dropLast).toFinset (path f).toFinset

namespace QMAPlanarListData
variable {G : QMARationalExchangeGraph} (P : QMAPlanarListData G)

def point (e : G.Edge) (k : ℕ) : ℕ × ℕ := (P.path e).getD k (0,0)

theorem point_get (e : G.Edge) {k : ℕ} (hk : k < (P.path e).length) :
    P.point e k = (P.path e)[k] := List.getD_eq_getElem _ _ hk

theorem point_mem (e : G.Edge) {k : ℕ} (hk : k < (P.path e).length) :
    P.point e k ∈ P.path e := by
  rw [P.point_get e hk]
  exact List.getElem_mem _

theorem point_interior (e : G.Edge) {k : ℕ} (hk0 : 0 < k) (hk : k < (P.path e).length-1) :
    P.point e k ∈ ((P.path e).drop 1).dropLast := by
  have hi : k-1 < (((P.path e).drop 1).dropLast).length := by
    simp only [List.length_dropLast,List.length_drop]
    omega
  have hm := List.getElem_mem (l := ((P.path e).drop 1).dropLast) hi
  rw [List.getElem_dropLast,List.getElem_drop] at hm
  simpa only [show 1+(k-1) = k from by omega,← P.point_get e (k := k) (by omega)] using hm

theorem point_disjoint (e f : G.Edge) (hef : e ≠ f) {i j : ℕ}
    (hi0 : 0 < i) (hi : i < (P.path e).length-1) (hj : j < (P.path f).length) :
    P.point e i ≠ P.point f j := by
  intro h
  have he := P.point_interior e hi0 hi
  rw [h] at he
  exact Finset.disjoint_left.mp (P.disjoint e f hef) (List.mem_toFinset.mpr he)
    (List.mem_toFinset.mpr (P.point_mem f hj))

def toRoute : QMAPlanarRouteData G where
  length e := (P.path e).length-1
  length_pos e := by have := P.length e; omega
  position := P.position
  position_injective := P.position_injective
  point := P.point
  positive e k hk := P.positive e _ (P.point_mem e (by have := P.length e; omega))
  first e := by
    have h := P.first e
    rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by have := P.length e; omega)] at h
    exact (P.point_get e (by have := P.length e; omega)).trans (Option.some.inj h)
  last e := by
    have h := P.last e
    rw [List.getLast?_eq_getElem?,List.getElem?_eq_getElem (by have := P.length e; omega)] at h
    exact (P.point_get e (by have := P.length e; omega)).trans (Option.some.inj h)
  simple e i j hi hj h := by
    have hi' : i < (P.path e).length := by have := P.length e; omega
    have hj' : j < (P.path e).length := by have := P.length e; omega
    rw [P.point_get e hi',P.point_get e hj'] at h
    exact (P.simple e).getElem_inj_iff.mp h
  step e i hi := by
    rw [P.point_get e (by omega),P.point_get e (by omega)]
    exact List.isChain_iff_getElem.mp (P.step e) i (by omega)
  avoids e i v hi0 hi := by
    intro h
    exact P.avoids e v (h ▸ P.point_interior e hi0 hi)
  disjoint e f i j hef hi0 hi hj :=
    P.point_disjoint e f hef hi0 hi (by have := P.length f; omega)
  edges_disjoint e f hef i j hi hj := by
    have hi' : i+1 < (P.path e).length := by omega
    have hj' : j+1 < (P.path f).length := by omega
    constructor
    · rintro ⟨h0,h1⟩
      by_cases h : i = 0
      · subst i
        exact P.point_disjoint e f hef (by omega) (by have := P.length e; omega) hj' h1
      · exact P.point_disjoint e f hef (by omega) hi (by omega) h0
    · rintro ⟨h0,h1⟩
      by_cases h : i = 0
      · subst i
        exact P.point_disjoint e f hef (by omega) (by have := P.length e; omega) (by omega) h1
      · exact P.point_disjoint e f hef (by omega) hi hj' h0

end QMAPlanarListData
end ContinuumCoulomb

end

end OAI
