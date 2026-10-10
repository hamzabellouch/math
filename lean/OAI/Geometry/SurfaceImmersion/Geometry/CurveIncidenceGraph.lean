import OAI.Geometry.SurfaceImmersion.Geometry.CurveEdgeWitness
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace OAI

/-! The bipartite incidence graph remembers distinct parallel interval edges. -/
noncomputable section
open Set
attribute [local instance] Classical.propDecidable
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X]

def curveIncidenceGraph (V : Set X) (P : Finset (Set X)) : SimpleGraph (V ⊕ P) where
  Adj a b := match a,b with
    | Sum.inl v, Sum.inr E => v.val ∈ closure E.val
    | Sum.inr E, Sum.inl v => v.val ∈ closure E.val
    | _,_ => False
  symm := ⟨by rintro (v|E) (w|F) h <;> exact h⟩
  loopless := ⟨by rintro (v|E) h <;> exact h⟩

@[simp] lemma curveIncidenceGraph_left_right (V : Set X) (P : Finset (Set X)) (v : V) (E : P) :
    (curveIncidenceGraph V P).Adj (Sum.inl v) (Sum.inr E) ↔ v.val ∈ closure E.val := Iff.rfl

lemma graph_degree_two {A : Type*} (G : SimpleGraph A) [Fintype A]
    (p a b : A) (hne : a ≠ b) (ha : G.Adj p a) (hb : G.Adj p b)
    (hall : ∀ z, G.Adj p z → z = a ∨ z = b) : G.degree p = 2 := by
  classical
  have hs : G.neighborSet p = {a,b} := by
    ext z
    constructor
    · exact hall z
    · rintro (rfl | hz)
      · exact ha
      · exact (mem_singleton_iff.mp hz) ▸ hb
  rw [← G.ncard_neighborSet,hs]
  simp [hne]

lemma curveIncidenceGraph_degree_left_one (V : Set X) (P : Finset (Set X)) [Fintype V]
    (v : V) (h : ∃ E ∈ P, v.val ∈ closure E ∧
      ∀ F ∈ P, v.val ∈ closure F → F = E) :
    (curveIncidenceGraph V P).degree (Sum.inl v) = 1 := by
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  obtain ⟨E,hE,hv,huniq⟩ := h
  refine ⟨Sum.inr ⟨E,hE⟩,hv,?_⟩
  rintro (w|F) hw
  · exact False.elim hw
  · exact congrArg Sum.inr (Subtype.ext (huniq F.val F.property hw))

lemma curveIncidenceGraph_degree_left_two (V : Set X) (P : Finset (Set X)) [Fintype V]
    (v : V) (h : ∃ E ∈ P, ∃ F ∈ P, E ≠ F ∧ v.val ∈ closure E ∧ v.val ∈ closure F ∧
      ∀ G ∈ P, v.val ∈ closure G → G = E ∨ G = F) :
    (curveIncidenceGraph V P).degree (Sum.inl v) = 2 := by
  obtain ⟨E,hE,F,hF,hne,hvE,hvF,hall⟩ := h
  apply graph_degree_two (curveIncidenceGraph V P) (Sum.inl v)
    (Sum.inr ⟨E,hE⟩) (Sum.inr ⟨F,hF⟩)
  · intro he
    exact hne (congrArg (fun z : P => z.val) (Sum.inr.inj he))
  · exact hvE
  · exact hvF
  · rintro (w|G) hg
    · exact False.elim hg
    · rcases hall G.val G.property hg with he | he
      · exact Or.inl (congrArg Sum.inr (Subtype.ext he))
      · exact Or.inr (congrArg Sum.inr (Subtype.ext he))

variable [T2Space X]
lemma curveIncidenceGraph_degree_right_two (V : Set X) (P : Finset (Set X)) [Fintype V]
    (E : P) (hdis : Disjoint E.val V) (w : CurveEdgeWitness V E.val) :
    (curveIncidenceGraph V P).degree (Sum.inr E) = 2 := by
  let l : V := ⟨w.leftPoint,w.left_mem⟩
  let r : V := ⟨w.rightPoint,w.right_mem⟩
  have hboundary : ∀ x ∈ V, x ∈ closure E.val ↔ x = w.leftPoint ∨ x = w.rightPoint := by
    intro x hxV
    have hn : x ∉ E.val := fun h => disjoint_left.mp hdis h hxV
    have h := w.frontier_eq
    constructor
    · intro hx
      have hb : x ∈ closure E.val \ E.val := ⟨hx,hn⟩
      rw [h] at hb
      simpa only [mem_insert_iff,mem_singleton_iff] using hb
    · intro hx
      have hb : x ∈ closure E.val \ E.val := by
        rw [h]
        simpa only [mem_insert_iff,mem_singleton_iff] using hx
      exact hb.1
  apply graph_degree_two (curveIncidenceGraph V P) (Sum.inr E) (Sum.inl l) (Sum.inl r)
  · intro he
    exact w.endpoints_ne (congrArg (fun z : V => z.val) (Sum.inl.inj he))
  · exact (hboundary _ w.left_mem).mpr (Or.inl rfl)
  · exact (hboundary _ w.right_mem).mpr (Or.inr rfl)
  · rintro (v|F) hv
    · rcases (hboundary _ v.property).mp hv with he | he
      · exact Or.inl (congrArg Sum.inl (Subtype.ext he))
      · exact Or.inr (congrArg Sum.inl (Subtype.ext he))
    · exact False.elim hv

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
