import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Block
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WalkBetweenSupport
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.WalkVertices
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Edges
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ActivityGapIndices

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
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma TreePath.active_reachable {w : NumericalLine D h ℓ} (P : TreePath w L)
    (hh : 0<h) (p : S.Index) (hph : ¬(p:ℕ) ∣ h) (a : ZMod (p:ℕ))
    (hactive : ∀ i,a+(P.vertex i : ZMod (p:ℕ))=0) :
    (edgeGraph w.line hh (litEdges w.line p a)).Reachable
      (P.vertex 0) (P.vertex (Fin.last P.length)) := by
  have hadj (i : Fin P.length) : (edgeGraph w.line hh (litEdges w.line p a)).Adj
      (P.vertex i.castSucc) (P.vertex i.succ) := by
    apply (active_graph_exact w.line hh p hph a _ _).mpr
    refine ⟨?_,hactive _,hactive _⟩
    obtain ⟨e,he,hev⟩ := P.adjacent hh i
    exact ⟨e,P.edges_subset he,hev⟩
  have aux (j : Fin (P.length+1)) :
      (edgeGraph w.line hh (litEdges w.line p a)).Reachable (P.vertex 0) (P.vertex j) := by
    induction j using Fin.induction with
    | zero => exact Reachable.refl _
    | succ i ih => exact ih.trans (hadj i).reachable
  exact aux _

lemma block_active_connected (w : NumericalLine D h ℓ) (hh : 0<h)
    (a : S.FixedResidues w.line) (H : Finset (Fin ℓ))
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (b : Block (edgeGraph w.line hh (w.line.treeSteps \ H))) (hb : b.walk.length ≤ L)
    (p : S.FixedIndex w.line) (hph : ¬(p.val:ℕ) ∣ h)
    {u v : ℤ} (hu : u ∈ treeVertices w.line) (hbu : u ∈ b.walk.support) (hbv : v ∈ b.walk.support)
    (hau : a p+(u : ZMod (p.val:ℕ))=0) (hav : a p+(v : ZMod (p.val:ℕ))=0) :
    (edgeGraph w.line hh (litEdges w.line p.val (a p))).Reachable u v := by
  by_cases huv : u=v
  · subst v; exact Reachable.refl _
  obtain ⟨q,hq⟩ := walk_between_support b.walk hbu hbv
  obtain ⟨P,h0,hn,he⟩ := exists_treePath w hh sdiff_subset q (hq.trans hb) hu huv
  have ha := P.all_active_of_no_gap a H hcut (fun i => (mem_sdiff.mp (he i)).2) p
    (by simpa only [h0] using hau) (by simpa only [hn] using hav)
  simpa only [h0,hn] using P.active_reachable hh p.val hph (a p) ha

theorem components_le_blocks (w : NumericalLine D h ℓ) (hh : 0<h)
    (a : S.FixedResidues w.line) (H : Finset (Fin ℓ))
    (hcut : ∀ (P : TreePath w L) (p : S.FixedIndex w.line),P.IsGap a p → ∃ i,P.edge i ∈ H)
    (bs : List (Block (edgeGraph w.line hh (w.line.treeSteps \ H))))
    (hbl : ∀ b ∈ bs,b.walk.length ≤ L)
    (hcover : ∀ v ∈ treeVertices w.line,∃ b ∈ bs,v ∈ b.walk.support)
    (p : S.FixedIndex w.line) (hph : ¬(p.val:ℕ) ∣ h) :
    (activeComponents w.line hh p.val (a p)).card ≤ bs.length := by
  let V := (treeVertices w.line).filter (fun v : ℤ => a p+(v:ZMod (p.val:ℕ))=0)
  let comp := (edgeGraph w.line hh (litEdges w.line p.val (a p))).connectedComponentMk
  let C := fun b : Block (edgeGraph w.line hh (w.line.treeSteps \ H)) =>
    (V.filter (fun v => v ∈ b.walk.support)).image comp
  have hC (b) (hb : b ∈ bs.toFinset) : (C b).card ≤ 1 := by
    apply card_le_one.mpr
    intro c hc d hd
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hc
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hd
    have huV := mem_filter.mp (mem_filter.mp hu).1
    have hvV := mem_filter.mp (mem_filter.mp hv).1
    exact ConnectedComponent.sound (block_active_connected w hh a H hcut b
      (hbl b (List.mem_toFinset.mp hb)) p hph huV.1 (mem_filter.mp hu).2
      (mem_filter.mp hv).2 huV.2 hvV.2)
  have hsub : activeComponents w.line hh p.val (a p) ⊆ bs.toFinset.biUnion C := by
    intro c hc
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hc
    obtain ⟨b,hb,hbv⟩ := hcover v (mem_filter.mp hv).1
    exact mem_biUnion.mpr ⟨b,List.mem_toFinset.mpr hb,mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hbv⟩,rfl⟩⟩
  calc
    (activeComponents w.line hh p.val (a p)).card ≤ (bs.toFinset.biUnion C).card := card_le_card hsub
    _ ≤ ∑ b ∈ bs.toFinset,(C b).card := card_biUnion_le
    _ ≤ ∑ _b ∈ bs.toFinset,1 := sum_le_sum hC
    _ = bs.toFinset.card := by simp
    _ ≤ bs.length := List.toFinset_card_le _

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
