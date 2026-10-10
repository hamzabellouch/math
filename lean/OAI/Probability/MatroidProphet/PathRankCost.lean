import OAI.Probability.MatroidProphet.CommonBudget
import OAI.Probability.MatroidProphet.Reverse.Paths
import OAI.Probability.MatroidProphet.LayerRank

namespace OAI

namespace MatroidProphet
open Set Finset
variable {α : Type*} [Fintype α]

lemma lowerCompetition_subset_guarded (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C T : ℕ → Set α) (b : ℤ) (h : ℕ) :
    lowerCompetition M hE κ D C T b h ⊆ guardedPath M hE κ D C h b := by
  induction h with
  | zero => exact Set.empty_subset _
  | succ h ih =>
    apply Set.union_subset
    · exact ih.trans ((guarded_subset_nominal M hE κ D C h b).trans
        (nominal_subset_guarded M hE κ D C h b))
    · exact fun _ he => nominal_subset_guarded M hE κ D C h b he.2.1

noncomputable def unobservedBirthRegion (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G O : Set α) (h : ℕ) (b : ℤ) : Set α :=
  if activation h + 2 ≤ b then
    (G ∩ (nominalPath M hE κ D C h b \ nominalPath M hE κ D C h (b-1))) \ O
  else ∅

lemma unobservedBirthRegion_subset (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D C : ℕ → Set α) (G O : Set α) (h : ℕ) (b : ℤ) :
    unobservedBirthRegion M hE κ D C G O h b ⊆ nominalPath M hE κ D C h b := by
  unfold unobservedBirthRegion
  split_ifs
  · exact fun _ he => he.1.2.1
  · exact Set.empty_subset _

theorem actual_path_rank_cost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C T : ℕ → Set α) (h later layers : ℕ)
    (start : ℤ) (S : ℤ → Set α)
    (hS : ∀ b, S b ⊆ nominalPath M hE κ D C h b) :
    κ * (∑ j ∈ range layers, conditionalRank M (S (start+2*j+2))
      (nominalPath M hE κ D C h (start+2*j) ∪
        lowerCompetition M hE κ D C T (start+2*j+2) h)) ≤
    κ * (∑ j ∈ range layers, conditionalRank M (S (start+2*j+2))
      (guardedPath M hE κ D C (h+1+later) (start+2*j) ∪
        lowerCompetition M hE κ D C T (start+2*j+2) h)) +
      κ * (C h).ncard +
        ∑ j ∈ range later, (κ * (C (h+1+j)).ncard + (D (h+1+j)).ncard) := by
  obtain ⟨J, hJcost, hJ⟩ := exists_commonPathBudget M hE κ hκ D C h later
  have hXfinal (b : ℤ) : nominalPath M hE κ D C h b ⊆
      guardedPath M hE κ D C (h+1+later) b := by
    apply (nominal_subset_guarded M hE κ D C h b).trans
    have hm : Monotone (fun j => guardedPath M hE κ D C j b) :=
      monotone_nat_of_le_succ (fun j => (guarded_subset_nominal M hE κ D C j b).trans
        (nominal_subset_guarded M hE κ D C j b))
    exact hm (by omega)
  have hr := rankCost_chain M J layers
    (fun j => nominalPath M hE κ D C h (start+2*j))
    (fun j => nominalPath M hE κ D C h (start+2*j) ∪
      lowerCompetition M hE κ D C T (start+2*j+2) h)
    (fun j => guardedPath M hE κ D C (h+1+later) (start+2*j) ∪
      lowerCompetition M hE κ D C T (start+2*j+2) h)
    (fun j => S (start+2*j+2))
    (fun _ _ => Set.subset_union_left)
    (fun j _ => Set.union_subset_union_left _ (hXfinal _))
    (by
      intro j hj
      apply Set.union_subset
      · exact (hJ _).trans (M.closure_subset_closure (by
          intro e he
          rcases he with he | he
          · exact Or.inl (Or.inl he)
          · exact Or.inr he))
      · intro e he
        exact M.mem_closure_of_mem (Or.inl (Or.inr he)) (by simp [hE]))
    (by
      intro j hj
      have heq : start+2*(↑(j+1):ℤ) = start+2*j+2 := by push_cast; omega
      rw [heq]
      apply Set.union_subset
      · apply Set.union_subset
        · exact nominalPath_mono M hE κ D C h (by omega)
        · exact (lowerCompetition_subset_guarded M hE κ D C T _ h).trans
            (guarded_subset_nominal M hE κ D C h _)
      · exact hS _)
  have hmul := Nat.mul_le_mul_left κ hr
  rw [Nat.mul_add] at hmul
  have hcard := natRank_le_ncard M J
  have hbound := (Nat.mul_le_mul_left κ hcard).trans hJcost
  omega

end MatroidProphet

end OAI
