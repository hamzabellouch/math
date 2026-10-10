import OAI.Probability.MatroidProphet.Residual.Generators
import OAI.Probability.MatroidProphet.RankAccounting

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

def commonPathGenerators (C J : ℕ → Set α) (h : ℕ) : ℕ → Set α
  | 0 => C h
  | t+1 => commonPathGenerators C J h t ∪ C (h+1+t) ∪ J (h+1+t)

omit [Fintype α] in
lemma commonPathGenerators_cost (κ : ℕ) (C D J : ℕ → Set α) (h t : ℕ)
    (hJ : ∀ j, κ * (J j).ncard ≤ (D j).ncard) :
    κ * (commonPathGenerators C J h t).ncard ≤ κ * (C h).ncard +
      ∑ j ∈ range t, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  induction t with
  | zero => simp [commonPathGenerators]
  | succ t ih =>
    have hcard := ncard_union_le (commonPathGenerators C J h t ∪ C (h+1+t)) (J (h+1+t))
    have hcard' := ncard_union_le (commonPathGenerators C J h t) (C (h+1+t))
    have hc : (commonPathGenerators C J h (t+1)).ncard ≤
        (commonPathGenerators C J h t).ncard + (C (h+1+t)).ncard + (J (h+1+t)).ncard := by
      exact hcard.trans (Nat.add_le_add_right hcard' _)
    have hm := Nat.mul_le_mul_left κ hc
    simp only [Nat.mul_add] at hm
    rw [sum_range_succ]
    have hj := hJ (h+1+t)
    omega

lemma commonPathGenerators_spans (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C J : ℕ → Set α) (h t : ℕ)
    (hJ : ∀ j k, nominalPath M hE κ D C j k ⊆
      M.closure (guardedPath M hE κ D C j k ∪ J j)) (k : ℤ) :
    guardedPath M hE κ D C (h+1+t) k ⊆
      M.closure (nominalPath M hE κ D C h k ∪ commonPathGenerators C J h t) := by
  induction t with
  | zero =>
    simp only [Nat.add_zero, commonPathGenerators, guardedPath_succ]
    exact M.closure_subset_closure (union_subset_union_right _ inter_subset_left)
  | succ t ih =>
    have hidx : h+1+(t+1) = (h+1+t)+1 := by omega
    rw [hidx, guardedPath_succ]
    apply M.closure_subset_closure_of_subset_closure
    apply Set.union_subset
    · apply (hJ (h+1+t) k).trans
      apply M.closure_subset_closure_of_subset_closure
      apply Set.union_subset
      · exact ih.trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl he
          · exact Or.inr (Or.inl (Or.inl he))))
      · intro e he
        exact M.mem_closure_of_mem (Or.inr (Or.inr he)) (by simp [hE])
    · intro e he
      exact M.mem_closure_of_mem (Or.inr (Or.inl (Or.inr he.1))) (by simp [hE])

theorem exists_commonPathBudget (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h t : ℕ) :
    ∃ Jtotal : Set α,
      κ * Jtotal.ncard ≤ κ * (C h).ncard +
        ∑ j ∈ range t, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) ∧
      ∀ k, guardedPath M hE κ D C (h+1+t) k ⊆
        M.closure (nominalPath M hE κ D C h k ∪ Jtotal) := by
  choose J hJD hcard τ htime hgen using
    (fun j => nominalPath_all_time_generators M hE κ hκ D C j)
  refine ⟨commonPathGenerators C J h t, commonPathGenerators_cost κ C D J h t hcard, ?_⟩
  intro k
  apply commonPathGenerators_spans M hE κ D C J h t _ k
  intro j l
  rw [hgen j l]
  apply M.closure_subset_closure
  exact union_subset_union_right _ (fun _ he => he.1)

end MatroidProphet

end OAI
