import OAI.Probability.MatroidProphet.Reverse.Iteration

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseNonexitCount (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → ℝ
  | 0, _, _, _ => 0
  | m+1, k, S, C => if stop k S then 0 else
      (if d ∈ (reverseStepTree M hE κ k D S G n).run C h then 1 else 0) +
        reverseNonexitCount M hE κ D G n stop d h m (k-1)
          ((reverseStepTree M hE κ k D S G n).run C) C

lemma reverseStepTree_contracts (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) (j : ℕ) :
    (reverseStepTree M hE κ k D S G n).run C j ⊆ S j := by
  rw [reverseStepTree_run]
  exact closed _ j

noncomputable def reverseStayEvent (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (d : α) (h : ℕ)
    (C : Finset α) : Prop :=
  d ∈ reverseNominal M hE κ D (fun j => (C : Set α) ∩ (G j : Set α)) S k h

omit [DecidableEq α] in
lemma reverseStayEvent_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S : ℕ → Set α) (G : ℕ → Finset α) (k : ℤ) (d : α) (h : ℕ) :
    Monotone (reverseStayEvent M hE κ D S G k d h) := by
  intro C C' hCC' he
  exact reverseNominal_mono M hE κ D _ _ S S le_rfl
    (fun j => Set.inter_subset_inter_left _ hCC') (fun _ => Set.Subset.rfl) h he

lemma reverseStepTree_nonexit_certificate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D S S₀ : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    {k k₀ : ℤ} (hk : k ≤ k₀) (hS : ∀ j, S j ⊆ S₀ j)
    (C : Finset α) (d : α) (h : ℕ)
    (he : d ∈ (reverseStepTree M hE κ k D S G n).run C h) :
    reverseStayEvent M hE κ D S₀ G k₀ d h
      (C ∩ (reverseStepTree M hE κ k D S G n).queried C) := by
  rw [reverseStepTree_run] at he
  rw [reverseStepTree_queried]
  exact reverseNominal_mono M hE κ D _ _ S S₀ hk
    (fun _ => Set.Subset.rfl) hS h he

lemma reverseNonexitCount_le_transactions (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ)
    (S₀ : ℕ → Set α) (k₀ : ℤ) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (hk : k ≤ k₀) (hS : ∀ j, S j ⊆ S₀ j) (closed : ReverseClosed M hE κ D k S)
    (C : Finset α) :
    reverseNonexitCount M hE κ D G n stop d h m k S C ≤
      (reverseTransactions M hE κ D G n stop m k S).run
        (reverseStayEvent M hE κ D S₀ G k₀ d h) C ∅ := by
  induction m generalizing k S with
  | zero => simp [reverseNonexitCount, reverseTransactions, QueryProgram.run]
  | succ m ih =>
    rw [reverseNonexitCount, reverseTransactions]
    by_cases hs : stop k S
    · simp only [ite_eq_left hs, QueryProgram.run, le_refl]
    · simp only [ite_eq_right hs]
      rw [RevealTree.transaction_run _ _ univ
        (reverseStepTree_fresh M hE κ k D S G n hG univ (fun _ _ => subset_univ _))]
      simp only [empty_union]
      apply add_le_add
      · by_cases he : d ∈ (reverseStepTree M hE κ k D S G n).run C h
        · rw [ite_eq_left he, ite_eq_left (reverseStepTree_nonexit_certificate M hE κ D S S₀ G n hk hS C d h he)]
        · rw [ite_eq_right he]
          split_ifs <;> norm_num
      · exact ih (k-1) _ (by omega)
          (fun j => (reverseStepTree_contracts M hE κ k D S G n closed C j).trans (hS j))
          (reverseStepTree_closed M hE κ k D S G n C)

theorem reverse_nonexit_budget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (d : α) (h : ℕ)
    (m : ℕ) (k₀ : ℤ) (S₀ : ℕ → Set α) (closed : ReverseClosed M hE κ D k₀ S₀)
    (q : α → ℝ) (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hδ : 0 < bitsFailure (reverseStayEvent M hE κ D S₀ G k₀ d h) q univ ∅) :
    bitsExpectation q univ (reverseNonexitCount M hE κ D G n stop d h m k₀ S₀) ≤
      Real.log (1 / bitsFailure (reverseStayEvent M hE κ D S₀ G k₀ d h) q univ ∅) := by
  apply le_trans (bitsExpectation_mono q hq0 hq1 univ
    (fun C _ => reverseNonexitCount_le_transactions M hE κ D G n hG stop d h S₀ k₀ m k₀ S₀
      le_rfl (fun _ => Set.Subset.rfl) closed C))
  exact disjoint_query_certificates_product _ (reverseStayEvent_mono M hE κ D S₀ G k₀ d h)
    q hq0 hq1 hδ _ (reverseTransactions_fresh M hE κ D G n hG stop m k₀ S₀ univ
      (fun _ _ => subset_univ _) closed)

end MatroidProphet

end OAI
