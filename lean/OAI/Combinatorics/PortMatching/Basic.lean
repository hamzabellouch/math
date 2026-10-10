import Mathlib.Combinatorics.SimpleGraph.Matching
import Lean.Elab.Tactic.Omega

namespace OAI

/-! Perfect-matching-preserving port-path degree reduction for finite simple graphs. -/

noncomputable section
namespace Matching205

universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev arity (v : V) : ℕ := Fintype.card (G.neighborSet v)
abbrev Vertex := (v : V) × Fin (2 * arity G v - 1)

def port (v : V) (w : G.neighborSet v) : Vertex G :=
  ⟨v, ⟨2 * ((Fintype.equivFin (G.neighborSet v)) w).val, by
    have h := ((Fintype.equivFin (G.neighborSet v)) w).isLt
    dsimp [arity] at *
    omega⟩⟩

def Internal (x y : Vertex G) : Prop :=
  x.1 = y.1 ∧ (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val)

def External (x y : Vertex G) : Prop :=
  ∃ h : G.Adj x.1 y.1,
    x = port G x.1 ⟨y.1, h⟩ ∧ y = port G y.1 ⟨x.1, h.symm⟩

lemma internal_symm {x y : Vertex G} (h : Internal G x y) : Internal G y x :=
  ⟨h.1.symm, h.2.symm⟩

lemma external_symm {x y : Vertex G} (h : External G x y) : External G y x := by
  obtain ⟨h, hx, hy⟩ := h
  exact ⟨h.symm, hy, hx⟩

def graph : SimpleGraph (Vertex G) where
  Adj x y := Internal G x y ∨ External G x y
  symm := ⟨fun _ _ h => h.elim (fun h => Or.inl (internal_symm G h))
    (fun h => Or.inr (external_symm G h))⟩
  loopless := ⟨by
    intro x h
    rcases h with h | ⟨h, _, _⟩
    · rcases h.2 with h | h <;> omega
    · exact G.irrefl h⟩

lemma port_adj {v w : V} (h : G.Adj v w) :
    (graph G).Adj (port G v ⟨w, h⟩) (port G w ⟨v, h.symm⟩) :=
  Or.inr ⟨h, rfl, rfl⟩

def decode (M : (graph G).Subgraph) : G.Subgraph where
  verts := Set.univ
  Adj v w := ∃ h : G.Adj v w,
    M.Adj (port G v ⟨w, h⟩) (port G w ⟨v, h.symm⟩)
  adj_sub := fun ⟨h, _⟩ => h
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨by
    intro v w h
    obtain ⟨h, hm⟩ := h
    exact ⟨h.symm, hm.symm⟩⟩

lemma decode_adj_iff (M : (graph G).Subgraph) (v w : V) :
    (decode G M).Adj v w ↔ ∃ h : G.Adj v w,
      M.Adj (port G v ⟨w, h⟩) (port G w ⟨v, h.symm⟩) := Iff.rfl

lemma card_fiber (v : V) : Fintype.card (Fin (2 * arity G v - 1)) =
    2 * G.degree v - 1 := by
  rw [Fintype.card_fin]
  change 2 * Fintype.card (G.neighborSet v) - 1 = 2 * G.degree v - 1
  rw [SimpleGraph.card_neighborSet_eq_degree]

end Matching205

end

end OAI
