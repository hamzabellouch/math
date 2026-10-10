import OAI.Probability.MatroidProphet.Reverse.Trace

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reversePrefixTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → RevealTree α (ℕ → Set α)
  | 0, _, S => .leaf S
  | m+1, k, S => (reverseStepTree M hE κ k D S G n).bind
      (fun S' => reversePrefixTree M hE κ D G n m (k-1) S')

lemma reversePrefixTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (V : Finset α)
    (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) :
    (reversePrefixTree M hE κ D G n m k S).Fresh V := by
  induction m generalizing k S V with
  | zero => trivial
  | succ m ih =>
    apply RevealTree.fresh_bind _ _ V (reverseStepTree_fresh M hE κ k D S G n hG V hV)
    intro C hC
    exact ih (k-1) _ _ (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
      (reverseStepTree_closed M hE κ k D S G n C)

lemma reversePrefixTree_remaining (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (V : Finset α)
    (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    ∀ j < n, (G j).filter (fun e => e ∈ (reversePrefixTree M hE κ D G n m k S).run C j) ⊆
      V \ (reversePrefixTree M hE κ D G n m k S).queried C := by
  induction m generalizing k S V C with
  | zero => simpa only [reversePrefixTree, RevealTree.run, RevealTree.queried, sdiff_empty] using hV
  | succ m ih =>
    rw [reversePrefixTree, RevealTree.run_bind, RevealTree.queried_bind]
    have hr := ih (k-1) _ _
      (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
      (reverseStepTree_closed M hE κ k D S G n C)
      (C \ (reverseStepTree M hE κ k D S G n).queried C)
    intro j hj e he
    have hx := mem_sdiff.mp (hr j hj he)
    have hy := mem_sdiff.mp hx.1
    exact mem_sdiff.mpr ⟨hy.1, fun hm => (mem_union.mp hm).elim hy.2 hx.2⟩

lemma reversePrefixTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    (reversePrefixTree M hE κ D G n m k S).run C = reverseFinal M hE κ D G n m k S C := by
  induction m generalizing k S C with
  | zero => rfl
  | succ m ih =>
    rw [reversePrefixTree, RevealTree.run_bind, reverseFinal]
    let W := univ \ (reverseStepTree M hE κ k D S G n).queried C
    have hW := reverseStepTree_remaining M hE κ k D S G n hG univ
      (fun _ _ => subset_univ _) closed C
    have hc := reverseStepTree_closed M hE κ k D S G n C
    have hcongr := (reversePrefixTree M hE κ D G n m (k-1)
      ((reverseStepTree M hE κ k D S G n).run C)).run_congr W
      (C \ (reverseStepTree M hE κ k D S G n).queried C) C
      (reversePrefixTree_fresh M hE κ D G n hG m (k-1) _ W hW hc)
      (fun e he => by
        have hne := (mem_sdiff.mp he).2
        simp only [mem_sdiff, hne, not_false_eq_true, and_true])
    rw [hcongr, ih (k-1) _ hc C]

theorem reversePrefixTree_tower (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (q : α → ℝ)
    (f : (ℕ → Set α) → Finset α → ℝ)
    (hf : ∀ R C C', (∀ j < n, ∀ e ∈ G j, e ∈ R j → (e ∈ C ↔ e ∈ C')) → f R C = f R C') :
    bitsExpectation q univ (fun C => f ((reversePrefixTree M hE κ D G n m k S).run C) C) =
      bitsExpectation q univ (fun C => bitsExpectation q univ
        (f ((reversePrefixTree M hE κ D G n m k S).run C))) := by
  let tree := reversePrefixTree M hE κ D G n m k S
  have hrem := reversePrefixTree_remaining M hE κ D G n hG m k S univ
    (fun _ _ => subset_univ _) closed
  have he : bitsExpectation q univ (fun C => f (tree.run C) C) =
      bitsExpectation q univ (fun C => f (tree.run C) (C \ tree.queried C)) := by
    apply bitsExpectation_congr
    intro C hC
    apply hf
    intro j hj e heG heR
    have hx := (mem_sdiff.mp (hrem C j hj (mem_filter.mpr ⟨heG, heR⟩))).2
    change e ∉ tree.queried C at hx
    simp only [mem_sdiff, hx, not_false_eq_true, and_true]
  rw [he, tree.continuation_expectation q univ
    (reversePrefixTree_fresh M hE κ D G n hG m k S univ (fun _ _ => subset_univ _) closed)]
  apply bitsExpectation_congr
  intro C hC
  symm
  apply bitsExpectation_restrict q univ _ (subset_univ _) (f (tree.run C))
  intro T T' hTT'
  apply hf
  intro j hj e heG heR
  exact hTT' e (hrem C j hj (mem_filter.mpr ⟨heG, heR⟩))

lemma reverseNominal_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (n : ℕ)
    (C C' : Finset α)
    (hC : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k n =
      reverseNominal M hE κ D (fun j => (C' : Set α) ∩ (G j : Set α)) S k n := by
  unfold reverseNominal
  congr 1
  apply reversePrefix_congr_guard_inter
  intro j hj
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · simp only [Set.mem_inter_iff, mem_coe, heG, heS, and_true, hC j hj e heG heS]
    · simp [heS]
  · simp [heG]

lemma reverseHybrid_mask_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (n : ℕ)
    (C C' T : Finset α)
    (hC : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C T) S k n =
      reverseNominal M hE κ D (transitionHybrid M hE κ k D S G C' T) S k n := by
  unfold reverseNominal
  congr 1
  apply reversePrefix_congr_guard_inter
  intro j hj
  have hn := reverseNominal_mask_congr M hE κ D S G k j C C'
    (fun i hi => hC i (by omega))
  ext e
  by_cases heG : e ∈ G j
  · by_cases heS : e ∈ S j
    · simp only [transitionHybrid, hn, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff,
        mem_coe, heG, heS, true_and, and_true, hC j hj e heG heS]
    · simp [heS]
  · simp [transitionHybrid, heG]

end MatroidProphet

end OAI
