import Mathlib.Combinatorics.SimpleGraph.Basic

namespace OAI

/-! A checked adjacency table gives a computable graph presentation whose
edge tests require only two array lookups. -/

namespace CycleClique.Construction
def adjacencyTableLookup (A : Array (Array Bool)) (i j : ℕ) : Bool :=
  (A.getD i #[]).getD j false

/-- Present `H` by a separately checked finite adjacency table. -/
def adjacencyTableGraph {n : ℕ} (H : SimpleGraph (Fin n))
    (A : Array (Array Bool))
    (hEq : ∀ i j : Fin n, H.Adj i j ↔ adjacencyTableLookup A i.val j.val = true) :
    SimpleGraph (Fin n) where
  Adj i j := adjacencyTableLookup A i.val j.val = true
  symm := ⟨fun i j hij => (hEq j i).mp ((hEq i j).mpr hij).symm⟩
  loopless := ⟨fun i hii => H.irrefl ((hEq i i).mpr hii)⟩

instance {n : ℕ} (H : SimpleGraph (Fin n)) (A : Array (Array Bool))
    (hEq : ∀ i j : Fin n, H.Adj i j ↔ adjacencyTableLookup A i.val j.val = true) :
    DecidableRel (adjacencyTableGraph H A hEq).Adj :=
  fun i j => inferInstanceAs (Decidable (adjacencyTableLookup A i.val j.val = true))

theorem adjacencyTableGraph_eq {n : ℕ} (H : SimpleGraph (Fin n))
    (A : Array (Array Bool))
    (hEq : ∀ i j : Fin n, H.Adj i j ↔ adjacencyTableLookup A i.val j.val = true) :
    adjacencyTableGraph H A hEq = H := by
  ext i j
  exact (hEq i j).symm

end CycleClique.Construction

end OAI
