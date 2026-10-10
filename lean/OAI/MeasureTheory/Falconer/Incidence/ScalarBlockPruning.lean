import OAI.MeasureTheory.Falconer.Estimates.ScalarChildChoice
import OAI.MeasureTheory.Falconer.Estimates.ScalarTaggedPrefix

namespace OAI

/-! One bottom-up scalar regularization step. Every surviving parent
 has the same branching and intermediate scale, with an explicit
 quadratic-in-block-width loss and unchanged deeper fibers. -/
namespace Falconer.Regularization

 theorem scalar_block_pruning {N a b : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (hab : a ≤ b) (hb : b ≤ N)
    (m : ℕ) (hm : ∀ c ∈ L.image (List.take b), (prefixFiber L b c).card = m) :
    ∃ K : CellPath 1 → Finset (CellPath 1), ∃ k n : ℕ,
      let Q := scalarPruneLeaves L a b K
      Q.Nonempty ∧ Q ⊆ L ∧ L.card ≤ 2050*(b-a+1)^2*Q.card ∧
      ∀ p ∈ Q.image (List.take a),
        ScalarChildChoice L a b p (K p) k n ∧
        prefixChildren Q a b p = K p ∧ (prefixFiber Q a p).card = 2^k*m := by
  classical
  let P := L.image (List.take a)
  have hex : ∀ p : CellPath 1, ∃ F k n, p ∈ P → ScalarChildChoice L a b p F k n := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨F,k,n,hdata⟩ := exists_scalar_child_choice L hL hab hb p hp
      exact ⟨F,k,n,fun _ => hdata⟩
    · exact ⟨∅,0,a,fun h => False.elim (hp h)⟩
  choose K k n hdata using hex
  let tag := fun p => (k p,n p)
  have htags : (P.image tag).card ≤ (b-a+1)^2 := by
    have hsub : P.image tag ⊆ (Finset.range (b-a+1)).product (Finset.Icc a b) := by
      intro t ht
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
      have hd := hdata p hp
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hd.2.2.1),
        Finset.mem_Icc.mpr ⟨hd.2.2.2.1,hd.2.2.2.2.1⟩⟩
    have hc : (Finset.Icc a b).card = b-a+1 := by rw [Nat.card_Icc]; omega
    calc
      _ ≤ ((Finset.range (b-a+1)).product (Finset.Icc a b)).card := Finset.card_le_card hsub
      _ = (Finset.range (b-a+1)).card*(Finset.Icc a b).card := Finset.card_product _ _
      _ = _ := by rw [Finset.card_range,hc,pow_two]
  obtain ⟨t,ht,hbound,_⟩ := scalar_tagged_prefix_prune L hne hab K tag 2050 ((b-a+1)^2) m
    (fun p hp => (hdata p hp).1) (fun p hp => (hdata p hp).2.2.2.2.2.1) hm htags
  let Kt := fun p => if tag p = t then K p else ∅
  let Q := scalarPruneLeaves L a b Kt
  have hQne : Q.Nonempty := by
    apply Finset.card_pos.mp
    have hc := hne.card_pos
    by_contra hh
    have hz : Q.card = 0 := by omega
    change L.card ≤ 2050*(b-a+1)^2*Q.card at hbound
    rw [hz,mul_zero] at hbound
    omega
  have hQsub : Q ⊆ L := scalarPruneLeaves_subset L a b Kt
  have hcommon : ∀ p ∈ Q.image (List.take a), p ∈ P ∧ tag p = t := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    refine ⟨Finset.mem_image_of_mem _ (hQsub hq),?_⟩
    have hh := (Finset.mem_filter.mp hq).2
    by_contra hqt
    simp only [Kt,ite_eq_right hqt,Finset.notMem_empty] at hh
  refine ⟨Kt,t.1,t.2,hQne,hQsub,hbound,?_⟩
  intro p hp
  have hcp := hcommon p hp
  have htag : (k p,n p) = t := hcp.2
  have hk : k p = t.1 := congrArg Prod.fst htag
  have hn : n p = t.2 := congrArg Prod.snd htag
  have hKt : Kt p = K p := by dsimp only [Kt]; rw [ite_eq_left hcp.2]
  have hd : ScalarChildChoice L a b p (Kt p) t.1 t.2 := by
    rw [hKt,← hk,← hn]
    exact hdata p hcp.1
  refine ⟨hd,scalarPruneLeaves_children L a b Kt p hd.1,?_⟩
  have hmass := scalarPruneLeaves_fiber_uniform L hab Kt p hd.1 m
    (fun c hc => hm c (prefixChildren_mem_image hc))
  rw [hd.2.1] at hmass
  exact hmass

end Falconer.Regularization

end OAI
