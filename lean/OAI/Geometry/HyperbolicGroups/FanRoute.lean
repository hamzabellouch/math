import Mathlib
import OAI.Geometry.HyperbolicGroups.CoreFan
import OAI.Geometry.HyperbolicGroups.CoreWordGraph

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry SimpleGraph

def base (i : Fin 7) : Fin 11 := ⟨i.val,lt_trans i.isLt (by decide)⟩
def common (i : Fin 7) : Fin 7 := ![1,2,1,6,2,1,6] i

lemma base_to_port (i l : Fin 7) (h : IsFanVertex i (.inr l)) :
    (graph (fan i)).Adj (.inl (base i)) (.inr l) := by
  have cert : ∀ i l : Fin 7, IsFanVertex i (.inr l) →
      ∃ e : IncidenceTemplate.Edge, e.val = (base i,l) ∧ e ∈ fan i := by decide
  exact cert i l h

lemma common_port (i : Fin 7) : IsFanVertex i (.inr (common i)) := by
  have cert : ∀ i : Fin 7, IsFanVertex i (.inr (common i)) := by decide
  exact cert i

lemma common_to_rep (i : Fin 7) (r : Fin 11) (h : IsFanVertex i (.inl r)) :
    (graph (fan i)).Adj (.inr (common i)) (.inl r) := by
  have cert : ∀ (i : Fin 7) (r : Fin 11), IsFanVertex i (.inl r) →
      ∃ e : IncidenceTemplate.Edge, e.val = (r,common i) ∧ e ∈ fan i := by decide
  exact cert i r h

/-- The source's fixed fan paths, length at most two, in the actual indexed
fan before its edge labels are identified in the bouquet. -/
def fanRoute (i : Fin 7) (v : FanVertex i) : (graph (fan i)).Walk (.inl (base i)) v.val := by
  rcases v with ⟨r|l,h⟩
  · exact .cons (base_to_port i (common i) (common_port i)) (.cons (common_to_rep i r h) .nil)
  · exact .cons (base_to_port i l h) .nil

lemma fanRoute_length (i : Fin 7) (v : FanVertex i) : (fanRoute i v).length ≤ 2 := by
  rcases v with ⟨r|l,h⟩ <;> simp [fanRoute]

/-- Inclusion in the core does not alter the orientation or the literal
random field used by an edge. -/
def inclusion (S : Finset IncidenceTemplate.Edge) : graph S →g graph Finset.univ where
  toFun := id
  map_rel' := by
    intro a b h
    cases a <;> cases b <;> try exact h.elim
    all_goals obtain ⟨e,he,hm⟩ := h; exact ⟨e,he,Finset.mem_univ _⟩

lemma inclusion_label (S : Finset IncidenceTemplate.Edge) (n : ℕ)
    (l : Field → LetterPresentation.Alphabet n) (e : (graph S).Dart) :
    label Finset.univ n l ((inclusion S).mapDart e) = label S n l e := by
  rcases e with ⟨⟨a,b⟩,h⟩
  cases a <;> cases b <;> try exact h.elim
  all_goals rfl

lemma inclusion_word (S : Finset IncidenceTemplate.Edge) (n : ℕ)
    (l : Field → LetterPresentation.Alphabet n) {a b : CoreGeometry.Vertex} (p : (graph S).Walk a b) :
    GraphWordFilling.word (label Finset.univ n l) (p.map (inclusion S)) =
      GraphWordFilling.word (label S n l) p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [SimpleGraph.Walk.map_cons,GraphWordFilling.word_cons,ih]; rfl

end HyperbolicObstruction.CoreWordGraph
end
end

section

end
end

end OAI
