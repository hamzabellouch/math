import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Block
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WalkVertices
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.AvoidEdgeSuffix

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
open OrdinaryCorrelations.ForestTraversal
open Finset Classical SimpleGraph
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K : ℕ}

structure CorruptWitness (w : NumericalLine D h ℓ) (p : S.Index) where
  edge : Fin ℓ
  tree : edge ∈ w.line.treeSteps
  divides : (p:ℕ) ∣ w.line.label edge
  vertex : Fin (ℓ+1)
  congruent : (w.line.offset vertex : ZMod (p:ℕ)) = (w.line.offset edge.castSucc : ZMod (p:ℕ))
  left_ne : w.line.offset vertex ≠ w.line.offset edge.castSucc
  right_ne : w.line.offset vertex ≠ w.line.offset edge.succ

lemma exists_corruptWitness (w : NumericalLine D h ℓ) (p : S.Index)
    (hp : freeCorrupted w.line p) : Nonempty (CorruptWitness w p) := by
  obtain ⟨_,e,he,hw⟩ := hp
  unfold ClosedLine.Uncorrupted at hw
  push Not at hw
  obtain ⟨j,hj,hleft,hright⟩ := hw
  exact ⟨⟨e,(mem_filter.mp he).1,(mem_filter.mp he).2,j,hj,hleft,hright⟩⟩

namespace CorruptWitness
variable {w : NumericalLine D h ℓ} {p : S.Index}

lemma near_path (c : CorruptWitness w p) (hh : 0<h) (hfree : ¬S.IsFixed w.line p)
    {s : ℤ} (hs : s=w.line.offset c.edge.castSucc ∨ s=w.line.offset c.edge.succ)
    (q : (edgeGraph w.line hh w.line.treeSteps).Walk s (w.line.offset c.vertex))
    (hlen : q.length ≤ K) :
    ∃ P : TreePath w K,
      (P.vertex 0=w.line.offset c.edge.castSucc ∨ P.vertex 0=w.line.offset c.edge.succ) ∧
      P.vertex (Fin.last P.length)=w.line.offset c.vertex ∧
      (∀ i, ¬(p:ℕ) ∣ w.line.label (P.edge i)) ∧
      ((p:ℕ):ℤ) ∣ P.vertex (Fin.last P.length)-P.vertex 0 := by
  let E := w.line.treeSteps \ {c.edge}
  have hremove : ∀ {u v},(edgeGraph w.line hh w.line.treeSteps).Adj u v →
      ¬(edgeGraph w.line hh E).Adj u v →
      (u=w.line.offset c.edge.castSucc ∧ v=w.line.offset c.edge.succ) ∨
      (u=w.line.offset c.edge.succ ∧ v=w.line.offset c.edge.castSucc) := by
    intro u v ha hn
    obtain ⟨e,he,hor⟩ := ha
    by_cases hec : e=c.edge
    · subst e
      rcases hor with hor | hor
      · exact Or.inl hor
      · exact Or.inr ⟨hor.2,hor.1⟩
    · exact (hn ⟨e,mem_sdiff.mpr ⟨he,by simpa using hec⟩,hor⟩).elim
  obtain ⟨u,hu,r,hr⟩ := avoid_edge_suffix hremove q
  have hu' : u=w.line.offset c.edge.castSucc ∨ u=w.line.offset c.edge.succ := by
    rcases hu with hu | hu
    · exact hu ▸ hs
    · exact hu
  have huv : u ∈ treeVertices w.line := by
    rcases hu' with rfl | rfl
    · exact departure_mem_vertices w.line c.edge
    · exact endpoint_mem_vertices w.line c.edge
  have hne : u≠w.line.offset c.vertex := by
    intro heq
    rcases hu' with hu | hu
    · exact c.left_ne (heq.symm.trans hu)
    · exact c.right_ne (heq.symm.trans hu)
  obtain ⟨P,hP0,hPL,hPE⟩ := exists_treePath w hh (show E ⊆ w.line.treeSteps from sdiff_subset)
    r (hr.trans hlen) huv hne
  refine ⟨P,hP0 ▸ hu',hPL,?_,?_⟩
  · intro i hi
    have hei := (unique_occurrence_of_free w.line p hfree c.edge c.divides (P.edge i)).mp hi
    exact (mem_sdiff.mp (hPE i)).2 (mem_singleton.mpr hei)
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p:ℕ)).mp
    rw [Int.cast_sub,hPL,hP0]
    apply sub_eq_zero.mpr
    rcases hu' with rfl | rfl
    · exact c.congruent
    · exact c.congruent.trans (w.line.label_residue_eq c.edge c.divides).symm

end CorruptWitness
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
