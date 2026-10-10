import OAI.Probability.MatroidProphet.Density.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

namespace MatroidProphet

open Set Finset

variable {α : Type*} [Fintype α]

noncomputable def conditionalRank (M : Matroid α) (S P : Set α) : ℕ :=
  natRank M (S ∪ P) - natRank M P

lemma conditionalRank_add_base (M : Matroid α) (S P : Set α) :
    conditionalRank M S P + natRank M P = natRank M (S ∪ P) := by
  exact Nat.sub_add_cancel (natRank_mono M subset_union_right)

lemma conditionalRank_antitone (M : Matroid α) (S : Set α)
    {P Q : Set α} (hPQ : P ⊆ Q) :
    conditionalRank M S Q ≤ conditionalRank M S P := by
  have hsub := natRank_submod M (S ∪ P) Q
  have hi := natRank_mono M (show P ⊆ (S ∪ P) ∩ Q from
    fun x hx => ⟨Or.inr hx, hPQ hx⟩)
  have hu : (S ∪ P) ∪ Q = S ∪ Q := by
    ext x
    simp only [mem_union]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (hPQ h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  rw [hu] at hsub
  have hP := conditionalRank_add_base M S P
  have hQ := conditionalRank_add_base M S Q
  omega

lemma conditionalRank_exchange (M : Matroid α) (S J A : Set α) :
    conditionalRank M S A + conditionalRank M J (A ∪ S) =
      conditionalRank M J A + conditionalRank M S (A ∪ J) := by
  have hSA := conditionalRank_add_base M S A
  have hJA := conditionalRank_add_base M J A
  have hJAS := conditionalRank_add_base M J (A ∪ S)
  have hSAJ := conditionalRank_add_base M S (A ∪ J)
  have hUS : S ∪ A = A ∪ S := union_comm _ _
  have hUJ : J ∪ A = A ∪ J := union_comm _ _
  have hU : J ∪ (A ∪ S) = S ∪ (A ∪ J) := by
    ext x
    simp only [mem_union]
    tauto
  rw [hUS] at hSA
  rw [hUJ] at hJA
  rw [hU] at hJAS
  omega

omit [Fintype α] in
lemma conditionalRank_closure (M : Matroid α) (S P : Set α) :
    conditionalRank M S (M.closure P) = conditionalRank M S P := by
  simp only [conditionalRank, natRank, M.eRk_union_closure_right_eq,
    M.eRk_closure_eq]

lemma conditionalRank_le_rank (M : Matroid α) (J A : Set α) :
    conditionalRank M J A ≤ natRank M J := by
  have h := conditionalRank_antitone M J (empty_subset A)
  simpa [conditionalRank] using h

lemma rankCost_step (M : Matroid α) (J S A B X Y : Set α)
    (hXA : X ⊆ A) (hAB : A ⊆ B)
    (hB : B ⊆ M.closure (A ∪ J)) (hY : A ∪ S ⊆ Y) :
    conditionalRank M S A - conditionalRank M S B ≤
      conditionalRank M J X - conditionalRank M J Y := by
  have hSJ := conditionalRank_antitone M S hB
  rw [conditionalRank_closure] at hSJ
  have hSA := conditionalRank_antitone M S hAB
  have hJA := conditionalRank_antitone M J hXA
  have hJY := conditionalRank_antitone M J hY
  have heq := conditionalRank_exchange M S J A
  omega

lemma sum_potential_drop_le (p : ℕ → ℕ) (m : ℕ)
    (hp : ∀ k < m, p (k + 1) ≤ p k) :
    (∑ k ∈ range m, (p k - p (k + 1))) ≤ p 0 := by
  suffices h : (∑ k ∈ range m, (p k - p (k + 1))) + p m = p 0 by omega
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hprev := ih (fun k hk => hp k (Nat.lt_trans hk (Nat.lt_succ_self m)))
    have hlast := hp m (Nat.lt_succ_self m)
    omega

lemma rankCost_chain (M : Matroid α) (J : Set α) (m : ℕ)
    (X A B S : ℕ → Set α)
    (hXA : ∀ k < m, X k ⊆ A k)
    (hAB : ∀ k < m, A k ⊆ B k)
    (hB : ∀ k < m, B k ⊆ M.closure (A k ∪ J))
    (hY : ∀ k < m, A k ∪ S k ⊆ X (k + 1)) :
    (∑ k ∈ range m, conditionalRank M (S k) (A k)) ≤
      (∑ k ∈ range m, conditionalRank M (S k) (B k)) + natRank M J := by
  have hmono : ∀ k < m, X k ⊆ X (k + 1) := by
    intro k hk
    exact (hXA k hk).trans (subset_union_left.trans (hY k hk))
  have hp : ∀ k < m, conditionalRank M J (X (k + 1)) ≤
      conditionalRank M J (X k) := fun k hk => conditionalRank_antitone M J (hmono k hk)
  have hdrop := sum_potential_drop_le (fun k => conditionalRank M J (X k)) m hp
  have hsum : (∑ k ∈ range m, conditionalRank M (S k) (A k)) ≤
      ∑ k ∈ range m, (conditionalRank M (S k) (B k) +
        (conditionalRank M J (X k) - conditionalRank M J (X (k + 1)))) := by
    apply sum_le_sum
    intro k hk
    have hk' := mem_range.1 hk
    have hs := rankCost_step M J (S k) (A k) (B k) (X k) (X (k + 1))
      (hXA k hk') (hAB k hk') (hB k hk') (hY k hk')
    have ha := conditionalRank_antitone M (S k) (hAB k hk')
    omega
  rw [sum_add_distrib] at hsum
  have hbound := conditionalRank_le_rank M J (X 0)
  omega

end MatroidProphet

end OAI
