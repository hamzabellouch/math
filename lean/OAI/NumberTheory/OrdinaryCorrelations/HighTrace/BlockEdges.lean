import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeEdge
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Block

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.NumericalSubtrees
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.ForestTraversal Finset Classical SimpleGraph
noncomputable section
variable {h ℓ : ℕ} {w : ClosedLine h ℓ} {hh : 0<h}

def blockEdges (b : Block (edgeGraph w hh w.treeSteps)) : Finset (Fin ℓ) :=
  w.treeSteps.filter (fun e => treeEdge w e ∈ b.walk.edges)
lemma blockEdges_subset (b : Block (edgeGraph w hh w.treeSteps)) : blockEdges b ⊆ w.treeSteps := filter_subset _ _

lemma block_edges_allowed (b : Block (edgeGraph w hh w.treeSteps)) :
    ∀ q ∈ b.walk.edges,q ∈ (edgeGraph w hh (blockEdges b)).edgeSet := by
  intro q hq
  have ha := b.walk.edges_subset_edgeSet hq
  induction q using Sym2.ind with | _ u v =>
    obtain ⟨e,he,hor | hrev⟩ := ha
    · have hqe : s(u,v)=treeEdge w e := by dsimp only at hor; unfold treeEdge; rw [hor.1,hor.2]
      exact ⟨e,mem_filter.mpr ⟨he,hqe ▸ hq⟩,Or.inl hor⟩
    · have hqe : s(u,v)=treeEdge w e := by dsimp only at hrev; unfold treeEdge; rw [hrev.1,hrev.2]; exact Sym2.eq_swap
      exact ⟨e,mem_filter.mpr ⟨he,hqe ▸ hq⟩,Or.inr hrev⟩

def localBlockWalk (b : Block (edgeGraph w hh w.treeSteps)) :
    (edgeGraph w hh (blockEdges b)).Walk b.1 b.2.1 := b.walk.transfer _ (block_edges_allowed b)
lemma localBlockWalk_support (b : Block (edgeGraph w hh w.treeSteps)) :
    (localBlockWalk b).support=b.walk.support := Walk.support_transfer ..
lemma localBlockWalk_length (b : Block (edgeGraph w hh w.treeSteps)) :
    (localBlockWalk b).length=b.walk.length := Walk.length_transfer ..

lemma block_edge_endpoints (b : Block (edgeGraph w hh w.treeSteps)) (e : Fin ℓ)
    (he : e ∈ blockEdges b) :
    w.offset e.castSucc ∈ b.walk.support ∧ w.offset e.succ ∈ b.walk.support := by
  have hm := (mem_filter.mp he).2
  constructor
  · exact Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨treeEdge w e,hm,by simp [treeEdge]⟩)
  · exact Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨treeEdge w e,hm,by simp [treeEdge]⟩)

end
end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
