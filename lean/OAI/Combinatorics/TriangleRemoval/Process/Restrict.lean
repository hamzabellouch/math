import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.ReindexSet
import OAI.Combinatorics.TriangleRemoval.Process.Within

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

def restrict (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) : BirthGraph s.card where
  older v := reindexSet s (B.older (s.orderEmbOfFin rfl v))
  older_lt v u hu := (s.orderEmbOfFin rfl).lt_iff_lt.mp
    (B.older_lt _ _ ((mem_reindexSet _ _ _).mp hu))
  older_card v := by
    rw [reindexSet_card (hclosed _ (s.orderEmbOfFin_mem rfl v))]
    exact B.older_card _

@[simp] lemma restrict_older_mem (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (u v : Fin s.card) :
    u ∈ (B.restrict s hclosed).older v ↔
      s.orderEmbOfFin rfl u ∈ B.older (s.orderEmbOfFin rfl v) :=
  mem_reindexSet _ _ _

@[simp] lemma restrict_graph_adj (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (u v : Fin s.card) :
    (B.restrict s hclosed).graph.Adj u v ↔
      B.graph.Adj (s.orderEmbOfFin rfl u) (s.orderEmbOfFin rfl v) := by
  simp only [graph_adj,restrict_older_mem]

lemma restrict_older_card (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (v : Fin s.card) :
    ((B.restrict s hclosed).older v).card = (B.older (s.orderEmbOfFin rfl v)).card :=
  reindexSet_card (hclosed _ (s.orderEmbOfFin_mem rfl v))

lemma restrict_within (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (Z : Finset (Fin N)) (hZ : Z ⊆ s)
    {x y : Fin N} (h : B.Within Z x y) (hx : x ∈ s) (hy : y ∈ s) :
    (B.restrict s hclosed).Within (reindexSet s Z)
      ((s.orderIsoOfFin rfl).symm ⟨x,hx⟩) ((s.orderIsoOfFin rfl).symm ⟨y,hy⟩) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head x z hxz _ ih =>
    have hz : z ∈ s := hZ hxz.2.1
    apply Relation.ReflTransGen.head (b := (s.orderIsoOfFin rfl).symm ⟨z,hz⟩) _ (ih hz)
    have hex : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨x,hx⟩) = x :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩)
    have hez : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨z,hz⟩) = z :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨z,hz⟩)
    simpa only [mem_reindexSet,restrict_older_mem,hex,hez] using hxz

lemma restrict_covered (s : Finset (Fin N))
    (hclosed : ∀ v ∈ s, B.older v ⊆ s) (Z : Finset (Fin N)) (hZ : Z ⊆ s)
    {a b : Fin N} (ha : a ∈ s) (hb : b ∈ s) (hc : B.Covered Z a b) :
    (B.restrict s hclosed).Covered (reindexSet s Z)
      ((s.orderIsoOfFin rfl).symm ⟨a,ha⟩) ((s.orderIsoOfFin rfl).symm ⟨b,hb⟩) := by
  intro i hi
  have hfi := (mem_reindexSet s Z i).mp hi
  have ha' : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨a,ha⟩) = a :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨a,ha⟩)
  have hb' : s.orderEmbOfFin rfl ((s.orderIsoOfFin rfl).symm ⟨b,hb⟩) = b :=
    congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨b,hb⟩)
  have hi' : (s.orderIsoOfFin rfl).symm ⟨s.orderEmbOfFin rfl i,hZ hfi⟩ = i := by
    exact (s.orderIsoOfFin rfl).symm_apply_apply i
  rcases hc _ hfi with ⟨haZ,hh⟩ | ⟨hbZ,hh⟩
  · refine Or.inl ⟨(mem_reindexSet s Z _).mpr (by rw [ha']; exact haZ),?_⟩
    simpa only [hi'] using B.restrict_within s hclosed Z hZ hh (hZ hfi) ha
  · refine Or.inr ⟨(mem_reindexSet s Z _).mpr (by rw [hb']; exact hbZ),?_⟩
    simpa only [hi'] using B.restrict_within s hclosed Z hZ hh (hZ hfi) hb

end SharpTerminalLeave.BirthGraph

end

end OAI
