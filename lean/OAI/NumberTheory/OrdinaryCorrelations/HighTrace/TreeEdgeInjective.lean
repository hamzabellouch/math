import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TreeEdge
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Append

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
variable {h ℓ : ℕ}

lemma treeEdge_injective (w : ClosedLine h ℓ) : Set.InjOn (treeEdge w) w.treeSteps := by
  intro e he f hf hef
  rcases Sym2.eq_iff.mp hef with hd | hs
  · exact tree_destination_injective w he hf hd.2
  · have hfe := incoming_earlier w hf hs.1.symm
    have hef := incoming_earlier w he hs.2
    exact (lt_asymm hfe hef).elim

lemma treeEdge_mem_edgeSet_iff (w : ClosedLine h ℓ) (hh : 0<h)
    {e : Fin ℓ} (he : e ∈ w.treeSteps) {E : Finset (Fin ℓ)} (hE : E ⊆ w.treeSteps) :
    treeEdge w e ∈ (edgeGraph w hh E).edgeSet ↔ e ∈ E := by
  constructor
  · rintro ⟨f,hf,hor | hrev⟩
    · have hef : treeEdge w e=treeEdge w f := by dsimp only at hor; unfold treeEdge; rw [hor.1,hor.2]
      exact treeEdge_injective w he (hE hf) hef ▸ hf
    · have hef : treeEdge w e=treeEdge w f := by dsimp only at hrev; unfold treeEdge; rw [hrev.1,hrev.2]; exact Sym2.eq_swap
      exact treeEdge_injective w he (hE hf) hef ▸ hf
  · intro heE
    exact edgeGraph_adj w hh E e heE

lemma tour_cutCount (w : ClosedLine h ℓ) (hh : 0<h) (H : Finset (Fin ℓ))
    (p : (edgeGraph w hh w.treeSteps).Walk 0 0)
    (hc : ∀ q : Sym2 ℤ,p.edges.count q=2*(w.treeSteps.filter (fun e => treeEdge w e=q)).card) :
    cutCount (edgeGraph w hh (w.treeSteps \ H)) p ≤ 2*H.card := by
  let F := p.edges.toFinset.filter (fun q => q ∉ (edgeGraph w hh (w.treeSteps \ H)).edgeSet)
  have hF : F ⊆ H.image (treeEdge w) := by
    intro q hq
    obtain ⟨hql,hqn⟩ := mem_filter.mp hq
    have ht := p.edges_subset_edgeSet (List.mem_toFinset.mp hql)
    induction q using Sym2.ind with | _ u v =>
      obtain ⟨e,he,hor | hrev⟩ := ht
      · have hqe : s(u,v)=treeEdge w e := by dsimp only at hor; unfold treeEdge; rw [hor.1,hor.2]
        refine mem_image.mpr ⟨e,?_,hqe.symm⟩
        by_contra hn
        exact hqn (hqe.symm ▸ (treeEdge_mem_edgeSet_iff w hh he sdiff_subset).mpr (mem_sdiff.mpr ⟨he,hn⟩))
      · have hqe : s(u,v)=treeEdge w e := by dsimp only at hrev; unfold treeEdge; rw [hrev.1,hrev.2]; exact Sym2.eq_swap
        refine mem_image.mpr ⟨e,?_,hqe.symm⟩
        by_contra hn
        exact hqn (hqe.symm ▸ (treeEdge_mem_edgeSet_iff w hh he sdiff_subset).mpr (mem_sdiff.mpr ⟨he,hn⟩))
  have hcount (q : Sym2 ℤ) : p.edges.count q ≤ 2 := by
    rw [hc]
    have hf : (w.treeSteps.filter (fun e => treeEdge w e=q)).card ≤ 1 := by
      apply card_le_one.mpr
      intro e he f hf
      exact treeEdge_injective w (mem_filter.mp he).1 (mem_filter.mp hf).1
        ((mem_filter.mp he).2.trans (mem_filter.mp hf).2.symm)
    omega
  calc
    cutCount (edgeGraph w hh (w.treeSteps \ H)) p = ∑ q ∈ F,p.edges.count q :=
      (sum_filter_count_eq_countP _ _).symm
    _ ≤ ∑ _q ∈ F,2 := sum_le_sum (fun q _ => hcount q)
    _ = 2*F.card := by simp [Nat.mul_comm]
    _ ≤ 2*H.card := Nat.mul_le_mul_left 2 ((card_le_card hF).trans card_image_le)

theorem tree_blocks (w : ClosedLine h ℓ) (hh : 0<h) (H : Finset (Fin ℓ))
    (L : ℕ) (hL : 0<L) :
    ∃ bs : List (Block (edgeGraph w hh (w.treeSteps \ H))),
      bs.length ≤ (2*ℓ)/L+2*H.card+1 ∧
      (∀ b ∈ bs,b.walk.length ≤ L) ∧
      (∀ z ∈ treeVertices w,∃ b ∈ bs,z ∈ b.walk.support) := by
  obtain ⟨p,hplen,hcover,hcount⟩ := grown_tour w hh 0 w.treeSteps (grows_full_tree w)
  obtain ⟨bs,hbs,hbl,hbc⟩ := chunk_cut_cover (edgeGraph w hh (w.treeSteps \ H)) L hL p
  refine ⟨bs,?_,hbl,?_⟩
  · have hcut := tour_cutCount w hh H p hcount
    have hcard : w.treeSteps.card ≤ ℓ := by simpa using card_le_univ w.treeSteps
    have hlen : p.length ≤ 2*ℓ := by rw [hplen]; omega
    exact hbs.trans (Nat.add_le_add_right (Nat.add_le_add (Nat.div_le_div_right hlen) hcut) 1)
  · intro z hz
    exact hbc.1 z (hcover z (reached_full_tree w ▸ hz))

end
end OrdinaryCorrelations.NumericalSubtrees

end

end OAI
