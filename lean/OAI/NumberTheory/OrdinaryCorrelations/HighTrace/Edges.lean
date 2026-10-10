import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UncutTreeEdges
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PathTop

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}
namespace TreePath
variable {w : NumericalLine D h ℓ}

def edges (P : TreePath w L) : Finset (Fin ℓ) := univ.image P.edge
lemma edge_mem (P : TreePath w L) (i : Fin P.length) : P.edge i ∈ P.edges := mem_image.mpr ⟨i,mem_univ _,rfl⟩
lemma edges_nonempty (P : TreePath w L) : P.edges.Nonempty :=
  ⟨P.edge ⟨0,P.length_pos⟩,P.edge_mem _⟩
lemma edges_subset (P : TreePath w L) : P.edges ⊆ w.line.treeSteps := by
  rintro e he
  obtain ⟨i,hi,rfl⟩ := mem_image.mp he
  exact P.tree i
lemma edge_origin_vertex (P : TreePath w L) (e : Fin ℓ) (he : e ∈ P.edges) :
    ∃ j, w.line.offset e.castSucc=P.vertex j := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp he
  have hh := P.endpoints i
  cases hf : P.forward i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at hh
  · exact ⟨i.succ,hh.2.symm⟩
  · exact ⟨i.castSucc,hh.1.symm⟩

lemma adjacent (P : TreePath w L) (hh : 0<h) (i : Fin P.length) :
    (edgeGraph w.line hh P.edges).Adj (P.vertex i.castSucc) (P.vertex i.succ) := by
  refine ⟨P.edge i,P.edge_mem i,?_⟩
  have he := P.endpoints i
  cases hf : P.forward i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at he
  · exact Or.inr ⟨he.2,he.1⟩
  · exact Or.inl he

lemma vertex_reachable (P : TreePath w L) (hh : 0<h) (i j : Fin (P.length+1)) :
    (edgeGraph w.line hh P.edges).Reachable (P.vertex i) (P.vertex j) := by
  have aux (i : Fin (P.length+1)) :
      (edgeGraph w.line hh P.edges).Reachable (P.vertex 0) (P.vertex i) := by
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ i ih => exact ih.trans (P.adjacent hh i).reachable
  exact (aux i).symm.trans (aux j)

lemma grows (P : TreePath w L) (hh : 0<h) : Grows w.line (pathTop w.line P.edges) P.edges := by
  refine ⟨P.edges_subset,?_⟩
  intro e he
  have ht : pathTop w.line P.edges ∉ P.edges.image (fun e => w.line.offset e.succ) := by
    simpa only [pathTop,dite_eq_left P.edges_nonempty] using min_origin_not_destination w.line P.edges_subset P.edges_nonempty
  obtain ⟨i,hi⟩ := P.edge_origin_vertex (P.edges.min' P.edges_nonempty) (min'_mem _ _)
  obtain ⟨j,hj⟩ := P.edge_origin_vertex e he
  have hv : (edgeGraph w.line hh P.edges).Reachable (pathTop w.line P.edges) (w.line.offset e.castSucc) := by
    simpa only [pathTop,dite_eq_left P.edges_nonempty,hi,hj] using P.vertex_reachable hh i j
  have hr := reachable_directed w.line hh P.edges_subset ht hv
  rcases hr.cases_tail with heq | ⟨z,hz,⟨k,hk,hkz,hke⟩⟩
  · exact Or.inl heq
  · exact Or.inr ⟨k,hk,incoming_earlier w.line (P.edges_subset hk) hke.symm,hke.symm⟩

lemma topMarks_card_le_two (P : TreePath w L) : (topMarks w.line P.edges).card ≤ 2 := by
  let I := univ.filter (fun i : Fin P.length => w.line.offset (P.edge i).castSucc=pathTop w.line P.edges)
  have he : topMarks w.line P.edges=I.image P.edge := by
    apply Finset.ext
    intro e
    constructor
    · intro he
      obtain ⟨heE,heT⟩ := mem_filter.mp he
      obtain ⟨i,hi,rfl⟩ := mem_image.mp heE
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,heT⟩,rfl⟩
    · intro he
      obtain ⟨i,hi,rfl⟩ := mem_image.mp he
      exact mem_filter.mpr ⟨P.edge_mem i,(mem_filter.mp hi).2⟩
  have hinj : Set.InjOn P.forward I := by
    intro i hi j hj hf
    have hir := (mem_filter.mp hi).2
    have hjr := (mem_filter.mp hj).2
    have hie := P.endpoints i
    have hje := P.endpoints j
    cases hfi : P.forward i
    · have hfj : P.forward j=false := hf.symm.trans hfi
      simp only [hfi,hfj,Bool.false_eq_true,ite_false] at hie hje
      have hij := P.distinct (hie.2.trans (hir.trans (hjr.symm.trans hje.2.symm)))
      exact Fin.succ_inj.mp hij
    · have hfj : P.forward j=true := hf.symm.trans hfi
      simp only [hfi,hfj,ite_true] at hie hje
      have hij := P.distinct (hie.1.trans (hir.trans (hjr.symm.trans hje.1.symm)))
      exact Fin.ext (congrArg (fun k : Fin (P.length+1) => k.val) hij)
  rw [he]
  apply (card_image_le).trans
  calc
    I.card = (I.image P.forward).card := (card_image_iff.mpr hinj).symm
    _ ≤ Fintype.card Bool := card_le_univ _
    _ = 2 := by simp

end TreePath
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
