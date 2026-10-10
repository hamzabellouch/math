import OAI.Probability.MatroidProphet.Reverse.Hybrid
import OAI.Probability.MatroidProphet.RevealComposition

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

omit [DecidableEq α] in
lemma reversePrefix_flat (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (j : ℕ) :
    M.IsFlat (reversePrefix M hE κ D C S k j) := by
  cases j with
  | zero =>
    by_cases hk : k < 0
    · simpa only [reversePrefix, ite_eq_left hk] using Matroid.isFlat_closure (M := M) ∅
    · simpa only [reversePrefix, ite_eq_right hk, ← hE] using M.ground_isFlat
  | succ j => exact Matroid.isFlat_closure (M := M) _

omit [DecidableEq α] in
lemma reverseNominal_flat (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C S : ℕ → Set α) (k : ℤ) (j : ℕ) :
    M.IsFlat (reverseNominal M hE κ D C S k j) :=
  densityEnabled_flat M hE κ (D j) (activation j) k (reversePrefix_flat M hE κ D C S k j)

omit [DecidableEq α] in

lemma reversePrefix_into_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C B S : ℕ → Set α) {l k : ℤ} (hlk : l ≤ k) (j : ℕ) :
    reversePrefix M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l j ⊆
      reversePrefix M hE κ D C S k j := by
  induction j with
  | zero => exact guardedPath_mono M hE κ D C 0 hlk
  | succ j ih =>
    have hn := densityEnabled_mono M hE κ (D j) (activation j) hlk ih
    have hs : reversePrefix M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l (j+1) ⊆
        reverseNominal M hE κ D C S k j := by
      exact (M.closure_subset_closure (Set.union_subset hn Set.inter_subset_right)).trans_eq
        (reverseNominal_flat M hE κ D C S k j).closure
    exact hs.trans (Set.subset_union_left.trans (M.subset_closure _ (by simp [hE])))

omit [DecidableEq α] in
lemma reverseNominal_into_output (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C B S : ℕ → Set α) {l k : ℤ} (hlk : l ≤ k) (j : ℕ) :
    reverseNominal M hE κ D B (fun i => reverseNominal M hE κ D C S k i) l j ⊆
      reverseNominal M hE κ D C S k j :=
  densityEnabled_mono M hE κ (D j) (activation j) hlk
    (reversePrefix_into_output M hE κ D C B S hlk j)

def ReverseClosed (M : Matroid α) (hE : M.E = Set.univ) (κ : ℕ)
    (D : ℕ → Set α) (k : ℤ) (S : ℕ → Set α) : Prop :=
  ∀ C j, reverseNominal M hE κ D C S k j ⊆ S j

omit [DecidableEq α] in
lemma reverseClosed_univ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (k : ℤ) :
    ReverseClosed M hE κ D k (fun _ => Set.univ) := fun _ _ => Set.subset_univ _

noncomputable def reverseStepTree (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    RevealTree α (ℕ → Set α) :=
  (sourceReverseTree M hE κ k D S G n).record.map
    (fun r j => reverseNominal M hE κ D (fun i => (r.positive : Set α) ∩ (G i : Set α)) S k j)

lemma reverseStepTree_run (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    (reverseStepTree M hE κ k D S G n).run C =
      (fun j => reverseNominal M hE κ D
        (fun i => ((C ∩ (sourceReverseTree M hE κ k D S G n).queried C : Finset α) : Set α) ∩ (G i : Set α)) S k j) := by
  rw [reverseStepTree, RevealTree.run_map, RevealTree.record_run]

lemma reverseStepTree_run_coordinate (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (C : Finset α) {j : ℕ} (hj : j ≤ n) :
    (reverseStepTree M hE κ k D S G n).run C j =
      reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) S k j := by
  rw [reverseStepTree_run]
  exact sourceReverseTree_positive_nominal M hE κ k D S G n hG C hj

lemma reverseStepTree_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V) :
    (reverseStepTree M hE κ k D S G n).Fresh V := by
  rw [reverseStepTree, RevealTree.fresh_map, RevealTree.record_fresh]
  exact sourceReverseTree_fresh M hE κ k D S G n hG V hV

lemma reverseStepTree_queried (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    (reverseStepTree M hE κ k D S G n).queried C =
      (sourceReverseTree M hE κ k D S G n).queried C := by
  rw [reverseStepTree, RevealTree.queried_map, RevealTree.record_queried]

lemma reverseStepTree_closed (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (C : Finset α) :
    ReverseClosed M hE κ D (k-1) ((reverseStepTree M hE κ k D S G n).run C) := by
  rw [reverseStepTree_run]
  intro B j
  exact reverseNominal_into_output M hE κ D _ B S (by omega) j

lemma reverseStepTree_remaining (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (k : ℤ) (D S : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    ∀ j < n, (G j).filter (fun e => e ∈ (reverseStepTree M hE κ k D S G n).run C j) ⊆
      V \ (reverseStepTree M hE κ k D S G n).queried C := by
  intro j hj e he
  rcases mem_filter.mp he with ⟨heG, heN⟩
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hj.le] at heN
  refine mem_sdiff.mpr ⟨hV j hj (mem_filter.mpr ⟨heG, closed _ j heN⟩), ?_⟩
  rw [reverseStepTree_queried,
    sourceReverseTree_queried_coordinate_full M hE κ k D S G n hG C hj heG]
  exact fun h => h.2 heN

noncomputable def reverseTransactions (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (stop : ℤ → (ℕ → Set α) → Prop) : ℕ → ℤ → (ℕ → Set α) → QueryProgram α
  | 0, _, _ => .stop
  | m+1, k, S => if stop k S then .stop else
      (reverseStepTree M hE κ k D S G n).transaction
        (fun S' => reverseTransactions M hE κ D G n stop m (k-1) S')

lemma reverseTransactions_fresh (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (stop : ℤ → (ℕ → Set α) → Prop) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (V : Finset α) (hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V)
    (closed : ReverseClosed M hE κ D k S) :
    (reverseTransactions M hE κ D G n stop m k S).Fresh V := by
  induction m generalizing k S V with
  | zero => trivial
  | succ m ih =>
    rw [reverseTransactions]
    split_ifs with hs
    · trivial
    · apply RevealTree.transaction_fresh _ _ V (reverseStepTree_fresh M hE κ k D S G n hG V hV)
      intro C hC
      exact ih (k-1) _ _ (reverseStepTree_remaining M hE κ k D S G n hG V hV closed C)
        (reverseStepTree_closed M hE κ k D S G n C)

end MatroidProphet

end OAI
