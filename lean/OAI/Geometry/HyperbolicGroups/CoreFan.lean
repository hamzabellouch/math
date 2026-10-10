import Mathlib
import OAI.Geometry.HyperbolicGroups.Template

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

/-- The actual vertices of the seven fan templates. The punctured D fan has
only its two non-CD ports. All representatives of its point are retained. -/
def IsFanVertex (i : Fin 7) : Vertex → Prop
  | .inl r => pointOfRepresentative r = i
  | .inr l => Incident i l ∧ (i,l) ≠ (3,4)

instance (i : Fin 7) (v : Vertex) : Decidable (IsFanVertex i v) := by
  cases v <;> unfold IsFanVertex <;> infer_instance

abbrev FanVertex (i : Fin 7) := {v : Vertex // IsFanVertex i v}

lemma card_fanVertex : ∀ i : Fin 7, Fintype.card (FanVertex i) = ![5,5,5,4,4,4,4] i := by
  decide

lemma card_fanVertex_le (i : Fin 7) : Fintype.card (FanVertex i) ≤ 5 := by
  rw [card_fanVertex]; fin_cases i <;> decide

lemma edge_fan_vertices (e : Edge) (i : Fin 7) (h : e ∈ fan i) :
    IsFanVertex i (.inl e.val.1) ∧ IsFanVertex i (.inr e.val.2) := by
  have certificate : ∀ (e : Edge) (i : Fin 7), e ∈ fan i →
      IsFanVertex i (.inl e.val.1) ∧ IsFanVertex i (.inr e.val.2) := by decide
  exact certificate e i h

/-- The undirected fan graph is a literal simple bipartite subgraph, not its
quotient by letter labels (which need not be injective). -/
def FanAdjacent (i : Fin 7) (a b : FanVertex i) : Prop := Adjacent a.val b.val
instance (i : Fin 7) (a b : FanVertex i) : Decidable (FanAdjacent i a b) :=
  inferInstanceAs (Decidable (Adjacent _ _))

def linePart : Vertex → Bool
  | .inl _ => false
  | .inr _ => true

lemma fanAdjacent_bipartite {i : Fin 7} {a b : FanVertex i} (h : FanAdjacent i a b) :
    linePart a.val ≠ linePart b.val := by
  rcases a with ⟨a,ha⟩; rcases b with ⟨b,hb⟩
  cases a <;> cases b <;> simp_all [FanAdjacent, Adjacent, linePart]

lemma fanAdjacent_ne {i : Fin 7} {a b : FanVertex i} (h : FanAdjacent i a b) : a ≠ b := by
  intro he; subst b; exact fanAdjacent_bipartite h rfl

/-- The edge index of a fan triangle is determined by its two radial labels.
This is independent of coincident generator values in the random row. -/
lemma index_unique {e f : Edge} (h :
    ({Sum.inl e.val.1, .inr e.val.2} : Finset Vertex) =
      {Sum.inl f.val.1, .inr f.val.2}) : e = f := by
  have h₁ : (Sum.inl e.val.1 : Vertex) ∈ ({Sum.inl f.val.1,Sum.inr f.val.2} : Finset Vertex) := by
    rw [← h]; simp
  have h₂ : (Sum.inr e.val.2 : Vertex) ∈ ({Sum.inl f.val.1,Sum.inr f.val.2} : Finset Vertex) := by
    rw [← h]; simp
  simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inl.injEq,Sum.inl_ne_inr,
    or_false] at h₁
  simp only [Finset.mem_insert,Finset.mem_singleton,Sum.inr.injEq,Sum.inr_ne_inl,
    false_or] at h₂
  exact Subtype.ext (Prod.ext h₁ h₂)

end CoreGeometry
end HyperbolicObstruction
end
end

section

end
end

end OAI
