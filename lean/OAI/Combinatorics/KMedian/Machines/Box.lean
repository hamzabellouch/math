import Mathlib
import OAI.Combinatorics.KMedian.Amplification.Amplifier
import OAI.Combinatorics.KMedian.Machines.BinaryReindex

namespace OAI

section Inline_PCPBox

namespace MetricKMedian.PCP.Amplifier
open scoped Classical

structure Box where
  nodes : ℕ
  edges : ℕ
  edges_pos : 0 < edges
  csp : BinaryCSP (Fin nodes) (Fin edges) Label
namespace Box
variable (C : Box)
instance edgeNonempty : Nonempty (Fin C.edges) := Fin.pos_iff_nonempty.mp C.edges_pos
def Perfect : Prop := ∃ a, C.csp.Satisfies a
def Rejects (δ : ℝ) : Prop := ∀ a, δ ≤ C.csp.rejection a
variable {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
noncomputable def ofCSP (D : BinaryCSP V E Label) : Box where
  nodes := Fintype.card V
  edges := Fintype.card E
  edges_pos := Fintype.card_pos
  csp := D.reindex (Fintype.equivFin V) (Fintype.equivFin E)
lemma ofCSP_complete (D : BinaryCSP V E Label) (h : ∃ a, D.Satisfies a) : (ofCSP D).Perfect := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a ∘ (Fintype.equivFin V).symm,D.reindex_complete _ _ a ha⟩
lemma ofCSP_sound (D : BinaryCSP V E Label) {δ : ℝ} (h : ∀ a, δ ≤ D.rejection a) :
    (ofCSP D).Rejects δ := by
  change ∀ a : Fin (Fintype.card V) → Label, δ ≤ (D.reindex (Fintype.equivFin V) (Fintype.equivFin E)).rejection a
  intro a
  rw [D.reindex_rejection]
  exact h _
lemma ofCSP_iff (D : BinaryCSP V E Label) : (ofCSP D).Perfect ↔ ∃ a, D.Satisfies a := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a ∘ (Fintype.equivFin V),(D.reindex_satisfies _ _ a).mp ha⟩
  · exact ofCSP_complete D
lemma ofCSP_nodes (D : BinaryCSP V E Label) : (ofCSP D).nodes=Nat.card V := Nat.card_eq_fintype_card.symm
lemma ofCSP_edges (D : BinaryCSP V E Label) : (ofCSP D).edges=Nat.card E := Nat.card_eq_fintype_card.symm
lemma ofCSP_edges_le (D : BinaryCSP V E Label) (n : ℕ) (h : Nat.card E ≤ n) :
    (ofCSP D).edges ≤ n := (ofCSP_edges D).le.trans h
lemma ofCSP_size_le (D : BinaryCSP V E Label) (n : ℕ) (h : Nat.card V+Nat.card E ≤ n) :
    (ofCSP D).nodes+(ofCSP D).edges ≤ n := by
  rw [ofCSP_nodes,ofCSP_edges]
  exact h

end Box
end MetricKMedian.PCP.Amplifier

end Inline_PCPBox

end OAI
