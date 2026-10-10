import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WalkBetweenSupport
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WalkVertices
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.BlockEdges
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AllForward

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
open OrdinaryCorrelations.ForestTraversal Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K : ℕ}
variable {w : NumericalLine D h ℓ} {hh : 0<h}

lemma TreePath.vertices_in_block (P : TreePath w K) (b : Block (edgeGraph w.line hh w.line.treeSteps))
    (hPE : ∀ i,P.edge i ∈ blockEdges b) : ∀ j,P.vertex j ∈ b.walk.support := by
  intro j
  cases j using Fin.cases with
  | zero =>
    let i : Fin P.length := ⟨0,P.length_pos⟩
    have hp := block_edge_endpoints b (P.edge i) (hPE i)
    have he := P.endpoints i
    have hi : i.castSucc=(0:Fin (P.length+1)) := rfl
    cases hf : P.forward i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at he
    · exact by simpa only [hi] using (he.1.symm ▸ hp.2)
    · exact by simpa only [hi] using (he.1.symm ▸ hp.1)
  | succ i =>
    have hp := block_edge_endpoints b (P.edge i) (hPE i)
    have he := P.endpoints i
    cases hf : P.forward i <;> simp only [hf,Bool.false_eq_true,ite_false,ite_true] at he
    · exact he.2.symm ▸ hp.1
    · exact he.2.symm ▸ hp.2

lemma block_root_paths (b : Block (edgeGraph w.line hh w.line.treeSteps))
    (hsmall : b.walk.length ≤ K) (hne : (blockEdges b).Nonempty) :
    ∃ c : Fin (ℓ+1),w.line.offset c ∈ b.walk.support ∧
      ∀ e ∈ blockEdges b,w.line.offset c=w.line.offset e.castSucc ∨
        ∃ P : TreePath w K,P.vertex 0=w.line.offset c ∧
          P.vertex (Fin.last P.length)=w.line.offset e.castSucc ∧
          (∀ i,P.edge i<e) := by
  let e₀ := (blockEdges b).min' hne
  let c := e₀.castSucc
  have hc : w.line.offset c ∈ b.walk.support :=
    (block_edge_endpoints b e₀ (min'_mem _ _)).1
  refine ⟨c,hc,?_⟩
  intro e he
  by_cases hv : w.line.offset c=w.line.offset e.castSucc
  · exact Or.inl hv
  · right
    have ht : w.line.offset e.castSucc ∈ b.walk.support := (block_edge_endpoints b e he).1
    obtain ⟨q,hq⟩ := walk_between_support (u := w.line.offset c) (v := w.line.offset e.castSucc) (localBlockWalk b)
      (by rwa [localBlockWalk_support]) (by rwa [localBlockWalk_support])
    have hlen : q.length ≤ K := by rw [localBlockWalk_length] at hq; exact hq.trans hsmall
    obtain ⟨P,hP0,hPL,hPE⟩ := exists_treePath w hh (blockEdges_subset b) q hlen
      (mem_image.mpr ⟨c,mem_univ _,rfl⟩) hv
    have hf : ∀ i,P.forward i=true := P.all_forward hPE (by
      rw [hP0]
      exact min_origin_not_destination w.line (blockEdges_subset b) hne)
    exact ⟨P,hP0,hPL,P.edges_before_endpoint hf e hPL⟩

lemma block_local_paths (b : Block (edgeGraph w.line hh w.line.treeSteps))
    (hsmall : b.walk.length ≤ K) (c v : Fin (ℓ+1))
    (hc : w.line.offset c ∈ b.walk.support) (hv : w.line.offset v ∈ b.walk.support) :
    w.line.offset c=w.line.offset v ∨ ∃ P : TreePath w K,
      P.vertex 0=w.line.offset c ∧ P.vertex (Fin.last P.length)=w.line.offset v ∧
      ∀ i,P.vertex i ∈ b.walk.support := by
  by_cases he : w.line.offset c=w.line.offset v
  · exact Or.inl he
  · right
    obtain ⟨q,hq⟩ := walk_between_support (u := w.line.offset c) (v := w.line.offset v) (localBlockWalk b)
      (by rwa [localBlockWalk_support]) (by rwa [localBlockWalk_support])
    have hlen : q.length ≤ K := by rw [localBlockWalk_length] at hq; exact hq.trans hsmall
    obtain ⟨P,hP0,hPL,hPE⟩ := exists_treePath w hh (blockEdges_subset b) q hlen
      (mem_image.mpr ⟨c,mem_univ _,rfl⟩) he
    exact ⟨P,hP0,hPL,P.vertices_in_block b hPE⟩

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
