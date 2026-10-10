import Mathlib

namespace OAI

/-!
# The finite coefficient argument in the high-entropy case

EKL (2006), Section 3, uses entropy symmetry to balance the row and column
sums of the root coefficients. The two-step root lemma makes a composed
positive edge full. The following finite argument then gives symmetric
coefficients, and full coefficients whenever a third vertex is involved.
-/

noncomputable section
open scoped BigOperators Classical

namespace DukePrimeDegree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma balanced_cut (w : ι → ι → ℝ)
    (hbal : ∀ i, ∑ j, w i j = ∑ j, w j i) (S : Finset ι) :
    (∑ i ∈ S, ∑ j ∈ Sᶜ, w i j) = ∑ i ∈ S, ∑ j ∈ Sᶜ, w j i := by
  have h := Finset.sum_congr (s₁ := S) rfl (fun i _ => hbal i)
  have hr (i : ι) : (∑ j, w i j) = (∑ j ∈ S, w i j) + ∑ j ∈ Sᶜ, w i j :=
    (Finset.sum_add_sum_compl S _).symm
  have hc (i : ι) : (∑ j, w j i) = (∑ j ∈ S, w j i) + ∑ j ∈ Sᶜ, w j i :=
    (Finset.sum_add_sum_compl S _).symm
  simp_rw [hr, hc, Finset.sum_add_distrib] at h
  have hi : (∑ i ∈ S, ∑ j ∈ S, w j i) = ∑ i ∈ S, ∑ j ∈ S, w i j := by
    rw [Finset.sum_comm]
  linarith

/-- A balanced nonnegative coefficient matrix with transitive positive
support cannot have a one-way positive edge. -/
theorem positive_support_symmetric_of_balanced
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hbal : ∀ i, ∑ j, w i j = ∑ j, w j i)
    (htrans : ∀ a b c, a ≠ c → 0 < w a b → 0 < w b c → 0 < w a c)
    {a b : ι} (hab : 0 < w a b) : 0 < w b a := by
  by_contra hba
  let S : Finset ι := Finset.univ.filter (fun i => i = a ∨ 0 < w i a)
  have haS : a ∈ S := by simp [S]
  have hbS : b ∈ Sᶜ := by
    simp only [Finset.mem_compl, S, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro (h | h)
    · subst b
      exact hba hab
    · exact hba h
  have hin : ∀ i ∈ S, ∀ j ∈ Sᶜ, w j i = 0 := by
    intro i hi j hj
    apply le_antisymm _ (hw j i)
    apply le_of_not_gt
    intro hji
    have hi' : i = a ∨ 0 < w i a := (Finset.mem_filter.mp hi).2
    have hj' : ¬ (j = a ∨ 0 < w j a) := by simpa only [Finset.mem_compl, S,
      Finset.mem_filter, Finset.mem_univ, true_and] using hj
    rcases hi' with rfl | hia
    · exact hj' (Or.inr hji)
    · by_cases hja : j = a
      · exact hj' (Or.inl hja)
      · exact hj' (Or.inr (htrans j i a hja hji hia))
  have hinzero : (∑ i ∈ S, ∑ j ∈ Sᶜ, w j i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact Finset.sum_eq_zero (fun j hj => hin i hi j hj)
  have houtzero : (∑ i ∈ S, ∑ j ∈ Sᶜ, w i j) = 0 := (balanced_cut w hbal S).trans hinzero
  have hterm : w a b ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j := by
    calc
      w a b ≤ ∑ j ∈ Sᶜ, w a j := Finset.single_le_sum (fun j _ => hw a j) hbS
      _ ≤ ∑ i ∈ S, ∑ j ∈ Sᶜ, w i j :=
        Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => hw i j) haS
  linarith

/-- A third neighbor makes a positive edge full, using the two-step rule. -/
theorem full_coefficient_of_third_neighbor
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hbal : ∀ i, ∑ j, w i j = ∑ j, w j i)
    (hcomp : ∀ a b c, a ≠ c → 0 < w a b → 0 < w b c → w a c = 1)
    {a b c : ι} (hab : a ≠ b) (_hac : a ≠ c) (hbc : b ≠ c)
    (hwab : 0 < w a b) (hwac : 0 < w a c) : w a b = 1 := by
  have htrans : ∀ i j k, i ≠ k → 0 < w i j → 0 < w j k → 0 < w i k := by
    intro i j k hik hij hjk
    rw [hcomp i j k hik hij hjk]
    norm_num
  have hwca := positive_support_symmetric_of_balanced w hw hbal htrans hwac
  have hwcb : w c b = 1 := hcomp c a b hbc.symm hwca hwab
  exact hcomp a c b hab hwac (by rw [hwcb]; norm_num)

/-- The entropy coefficients are symmetric once the row balance and the
geometric two-step root rule have been established. -/
theorem coefficients_symmetric_of_balanced_two_step
    (w : ι → ι → ℝ) (hw : ∀ i j, 0 ≤ w i j)
    (hbal : ∀ i, ∑ j, w i j = ∑ j, w j i)
    (hcomp : ∀ a b c, a ≠ c → 0 < w a b → 0 < w b c → w a c = 1) :
    ∀ a b, w a b = w b a := by
  have htrans : ∀ i j k, i ≠ k → 0 < w i j → 0 < w j k → 0 < w i k := by
    intro i j k hik hij hjk
    rw [hcomp i j k hik hij hjk]
    norm_num
  have hsymm := @positive_support_symmetric_of_balanced ι _ _ w hw hbal htrans
  intro a b
  by_cases hab : a = b
  · subst b
    rfl
  by_cases hwab : 0 < w a b
  · have hwba := hsymm hwab
    by_cases hex : ∃ c, c ≠ a ∧ c ≠ b ∧ 0 < w a c
    · obtain ⟨c, hca, hcb, hwac⟩ := hex
      have h₁ := full_coefficient_of_third_neighbor w hw hbal hcomp hab hca.symm hcb.symm hwab hwac
      have hwbc : 0 < w b c := htrans b a c hcb.symm hwba hwac
      have h₂ := full_coefficient_of_third_neighbor w hw hbal hcomp (Ne.symm hab) hcb.symm hca.symm hwba hwbc
      exact h₁.trans h₂.symm
    · have heq : ∀ c ∈ Finset.univ.erase b, w a c = w c a := by
        intro c hc
        by_cases hca : c = a
        · subst c
          rfl
        have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
        have hnot : ¬ 0 < w a c := fun h => hex ⟨c, hca, hcb, h⟩
        have hnot' : ¬ 0 < w c a := fun h => hnot (hsymm h)
        exact (le_antisymm (le_of_not_gt hnot) (hw a c)).trans
          (le_antisymm (le_of_not_gt hnot') (hw c a)).symm
      have hrest := Finset.sum_congr (s₁ := Finset.univ.erase b) rfl heq
      have hrow := Finset.sum_erase_add Finset.univ (fun c => w a c) (Finset.mem_univ b)
      have hcol := Finset.sum_erase_add Finset.univ (fun c => w c a) (Finset.mem_univ b)
      have hbalance := hbal a
      linarith
  · have hnot' : ¬ 0 < w b a := fun h => hwab (hsymm h)
    exact (le_antisymm (le_of_not_gt hwab) (hw a b)).trans
      (le_antisymm (le_of_not_gt hnot') (hw b a)).symm

end DukePrimeDegree

end

end OAI
