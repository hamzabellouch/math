import Mathlib
import OAI.Combinatorics.ThinTrees.Signing.Realization

namespace OAI

/-! Greedy tree. -/

section

namespace AlgorithmicThinTrees.GreedyTree
open Finset StrongThinTree StrongThinTree.MultiGraph
variable {n m : ℕ}

def expand (G : MultiGraph n m) (A : Finset (Fin m)) (U : Finset (Fin n)) :
    Finset (Fin n) :=
  U ∪ (A.filter (fun e => G.right e ∈ U)).image G.left ∪
    (A.filter (fun e => G.left e ∈ U)).image G.right

def reach (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) (t : ℕ) : Finset (Fin n) :=
  (expand G A)^[t] {root}

lemma subset_expand (G : MultiGraph n m) (A : Finset (Fin m)) (U : Finset (Fin n)) :
    U ⊆ expand G A U := (subset_union_left).trans subset_union_left

lemma reach_succ (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) (t : ℕ) :
    reach G A root (t+1)=expand G A (reach G A root t) := Function.iterate_succ_apply' _ _ _

lemma reach_mono (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) :
    Monotone (reach G A root) :=
  monotone_nat_of_le_succ (fun t => (reach_succ G A root t).symm ▸ subset_expand G A _)

lemma reach_root (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) (t : ℕ) :
    root ∈ reach G A root t := reach_mono G A root (Nat.zero_le t) (mem_singleton_self root)

lemma expand_strict (G : MultiGraph n m) (A : Finset (Fin m)) (hc : G.Connected A)
    (U : Finset (Fin n)) (hu : U.Nonempty) (hu' : U ≠ univ) : U ⊂ expand G A U := by
  obtain ⟨e,he⟩ := hc U hu hu'
  obtain ⟨hea,hcut⟩ := mem_filter.mp he
  apply ssubset_iff_subset_ne.mpr
  refine ⟨subset_expand G A U,?_⟩
  intro heq
  rcases hcut with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · apply hr
    rw [heq]
    exact mem_union_right _ (mem_image.mpr ⟨e,mem_filter.mpr ⟨hea,hl⟩,rfl⟩)
  · apply hl
    rw [heq]
    exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨e,mem_filter.mpr ⟨hea,hr⟩,rfl⟩))

lemma reach_full (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n)
    (hc : G.Connected A) : reach G A root n=univ := by
  by_contra hne
  have hstrict (i : ℕ) (hi : i ≤ n) : reach G A root i ≠ univ := by
    intro he
    apply hne
    exact eq_univ_iff_forall.mpr (fun v => reach_mono G A root hi (he ▸ mem_univ v))
  have hcard : ∀i, i ≤ n → i+1 ≤ (reach G A root i).card := by
    intro i hi
    induction i with
    | zero => simp [reach]
    | succ i ih =>
      have hj := ih (by omega)
      have hs := card_lt_card (expand_strict G A hc (reach G A root i)
        ⟨root,reach_root G A root i⟩ (hstrict i (by omega)))
      rw [reach_succ]
      omega
  have hh := (hcard n le_rfl).trans (card_le_univ _)
  simp only [Fintype.card_fin] at hh
  omega

lemma reach_same (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) (t : ℕ) :
    ∀v ∈ reach G A root t, G.Same A v root := by
  induction t with
  | zero =>
    intro v hv
    have he : v=root := mem_singleton.mp hv
    subst v
    exact G.same_refl A root
  | succ t ih =>
    intro v hv
    rw [reach_succ] at hv
    rcases mem_union.mp hv with hv|hv
    · rcases mem_union.mp hv with hv|hv
      · exact ih v hv
      · obtain ⟨e,he,rfl⟩ := mem_image.mp hv
        obtain ⟨he,hu⟩ := mem_filter.mp he
        exact G.same_trans (G.same_endpoints he) (ih _ hu)
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hv
      obtain ⟨he,hu⟩ := mem_filter.mp he
      exact G.same_trans (G.same_symm (G.same_endpoints he)) (ih _ hu)

lemma connected_iff_reach (G : MultiGraph n m) (A : Finset (Fin m)) (root : Fin n) :
    G.Connected A ↔ reach G A root n=univ := by
  refine ⟨reach_full G A root,fun h => ?_⟩
  rw [G.connected_iff_same]
  intro u v
  exact G.same_trans (reach_same G A root n u (h ▸ mem_univ _))
    (G.same_symm (reach_same G A root n v (h ▸ mem_univ _)))

def connected (G : MultiGraph n m) (A : Finset (Fin m)) : Bool :=
  if hn : 0 < n then decide (reach G A ⟨0,hn⟩ n=univ) else true

lemma connected_correct (G : MultiGraph n m) (A : Finset (Fin m)) :
    connected G A=true ↔ G.Connected A := by
  unfold connected
  split_ifs with hn
  · simpa only [decide_eq_true_eq] using (connected_iff_reach G A ⟨0,hn⟩).symm
  · have hzero : n=0 := by omega
    subst n
    simp only [true_iff]
    intro S hS _
    obtain ⟨v,_⟩ := hS
    exact Fin.elim0 v

lemma connected_mono (G : MultiGraph n m) {A B : Finset (Fin m)} (h : A ⊆ B)
    (hc : G.Connected A) : G.Connected B := by
  intro S hS hS'
  exact (hc S hS hS').mono (filter_subset_filter _ h)

def eraseIf (G : MultiGraph n m) (A : Finset (Fin m)) (e : Fin m) : Finset (Fin m) :=
  if connected G (A.erase e) then A.erase e else A

def deletePass (G : MultiGraph n m) (A : Finset (Fin m)) (es : List (Fin m)) : Finset (Fin m) :=
  es.foldl (eraseIf G) A

def tree (G : MultiGraph n m) : Finset (Fin m) := deletePass G univ (List.finRange m)

lemma eraseIf_subset (G : MultiGraph n m) (A : Finset (Fin m)) (e : Fin m) :
    eraseIf G A e ⊆ A := by
  unfold eraseIf
  split_ifs <;> simp only [erase_subset,Subset.refl]

lemma eraseIf_connected (G : MultiGraph n m) (A : Finset (Fin m)) (hc : G.Connected A)
    (e : Fin m) : G.Connected (eraseIf G A e) := by
  unfold eraseIf
  split_ifs with hh
  · exact (connected_correct G (A.erase e)).mp hh
  · exact hc

lemma deletePass_correct (G : MultiGraph n m) (es : List (Fin m))
    (A : Finset (Fin m)) (hc : G.Connected A) :
    deletePass G A es ⊆ A ∧ G.Connected (deletePass G A es) ∧
      ∀e ∈ es, e ∈ deletePass G A es → ¬G.Connected ((deletePass G A es).erase e) := by
  induction es generalizing A with
  | nil => exact ⟨subset_rfl,hc,by simp⟩
  | cons e es ih =>
    rw [deletePass,List.foldl_cons]
    change deletePass G (eraseIf G A e) es ⊆ A ∧ _
    obtain ⟨hsub,hconn,hmin⟩ := ih (eraseIf G A e) (eraseIf_connected G A hc e)
    refine ⟨hsub.trans (eraseIf_subset G A e),hconn,?_⟩
    intro f hf hmem hcon
    rcases List.mem_cons.mp hf with rfl|hf
    · have heA : f ∈ eraseIf G A f := hsub hmem
      have hbad : connected G (A.erase f)≠true := by
        intro he
        simp only [eraseIf,he,ite_true,mem_erase,ne_eq,not_true_eq_false,false_and] at heA
      apply hbad
      apply (connected_correct G (A.erase f)).mpr
      exact connected_mono G (erase_subset_erase _ (hsub.trans (eraseIf_subset G A f))) hcon
    · exact hmin f hf hmem hcon

theorem tree_correct (G : MultiGraph n m) (hc : G.Connected univ) : G.SpanningTree (tree G) := by
  obtain ⟨_,hconn,hmin⟩ := deletePass_correct G (List.finRange m) univ hc
  refine ⟨hconn,?_⟩
  intro e he
  exact hmin e (List.mem_finRange _) he

end AlgorithmicThinTrees.GreedyTree
end

end OAI
