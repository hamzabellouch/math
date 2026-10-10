import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Basic.Real.Basic

namespace OAI

/-!
# Counting finite words by their color profiles

The coefficient attached to a profile is the actual cardinality of its fiber
among finite words. Regrouping the weighted sum over words proves the finite
multinomial identity without introducing a factorial formula or a counting
hypothesis.
-/

namespace TalagrandThreshold

open scoped BigOperators

/-- The number of positions of each color in a word on a finite domain. -/
def wordProfile {D H : Type*} [Fintype D] [DecidableEq H] (f : D → H) (h : H) : ℕ :=
  (Finset.univ.filter fun i => f i = h).card

/-- All words on a fixed finite domain having the specified profile. -/
def wordFiber (D : Type*) {H : Type*} [Fintype D] [DecidableEq D]
    [Fintype H] [DecidableEq H] (n : H → ℕ) : Finset (D → H) :=
  Finset.univ.filter fun f => wordProfile f = n

/-- The concrete multinomial coefficient, defined as a finite fiber cardinality. -/
def wordCount {H : Type*} [Fintype H] [DecidableEq H] (t : ℕ) (n : H → ℕ) : ℕ :=
  (wordFiber (Fin t) n).card

/-- The finite set of profiles attained by words of length `t`. -/
def wordProfiles (H : Type*) [Fintype H] [DecidableEq H] (t : ℕ) : Finset (H → ℕ) :=
  Finset.univ.image (fun f : Fin t → H => wordProfile f)

variable {H : Type*} [Fintype H] [DecidableEq H]

@[simp] theorem mem_wordFiber (D : Type*) [Fintype D] [DecidableEq D]
    (n : H → ℕ) (f : D → H) : f ∈ wordFiber D n ↔ wordProfile f = n := by
  simp only [wordFiber, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_wordProfiles_iff (t : ℕ) (n : H → ℕ) :
    n ∈ wordProfiles H t ↔ ∃ f : Fin t → H, wordProfile f = n := by
  simp only [wordProfiles, Finset.mem_image, Finset.mem_univ, true_and]

theorem sum_wordProfile {D : Type*} [Fintype D] (f : D → H) :
    (∑ h, wordProfile f h) = Fintype.card D := by
  simpa only [wordProfile, Finset.mem_univ, Finset.filter_true, Finset.card_univ] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset D) Finset.univ f)

theorem wordCount_eq_zero_of_not_mem_wordProfiles (t : ℕ) (n : H → ℕ)
    (hn : n ∉ wordProfiles H t) : wordCount t n = 0 := by
  unfold wordCount wordFiber
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro f _ hf
  exact hn ((mem_wordProfiles_iff t n).mpr ⟨f, hf⟩)

/-- The weight from a profile equals the product of the individual letter weights. -/
theorem prod_weight_wordProfile {D : Type*} [Fintype D]
    (f : D → H) (π : H → ℝ) :
    (∏ h, π h ^ wordProfile f h) = ∏ i, π (f i) := by
  simpa only [wordProfile, Finset.prod_const] using
    (Finset.prod_fiberwise' (Finset.univ : Finset D) f π)

/-- The multinomial identity obtained by grouping actual words by their profile. -/
theorem sum_wordCount_weight (t : ℕ) (π : H → ℝ) :
    (∑ n ∈ wordProfiles H t, (wordCount t n : ℝ) * ∏ h, π h ^ n h) =
      (∑ h, π h) ^ t := by
  have hgroup : (∑ f : Fin t → H, ∏ h, π h ^ wordProfile f h) =
      ∑ n ∈ wordProfiles H t, (wordCount t n : ℝ) * ∏ h, π h ^ n h := by
    simpa only [wordProfiles, wordCount, wordFiber, nsmul_eq_mul] using
      (Finset.sum_comp (s := (Finset.univ : Finset (Fin t → H)))
        (fun n : H → ℕ => ∏ h, π h ^ n h) (fun f : Fin t → H => wordProfile f))
  calc
    _ = ∑ f : Fin t → H, ∏ h, π h ^ wordProfile f h := hgroup.symm
    _ = ∑ f : Fin t → H, ∏ i, π (f i) := by
      apply Finset.sum_congr rfl
      intro f _
      exact prod_weight_wordProfile f π
    _ = (∑ h, π h) ^ t := (Fintype.sum_pow π t).symm

theorem wordCount_weight_nonneg (t : ℕ) (π : H → ℝ) (hπ : ∀ h, 0 ≤ π h)
    (n : H → ℕ) : 0 ≤ (wordCount t n : ℝ) * ∏ h, π h ^ n h :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun h _ => pow_nonneg (hπ h) _)

theorem sum_wordCount_weight_le_one (t : ℕ) (π : H → ℝ) (hπ : ∀ h, 0 ≤ π h)
    (hπsum : (∑ h, π h) ≤ 1) :
    (∑ n ∈ wordProfiles H t, (wordCount t n : ℝ) * ∏ h, π h ^ n h) ≤ 1 := by
  rw [sum_wordCount_weight]
  exact pow_le_one₀ (Finset.sum_nonneg fun h _ => hπ h) hπsum

/-- Any finite collection of profiles has total weight at most one, including
profiles not attained by a word: their fiber counts are zero. -/
theorem sum_wordCount_weight_finset_le_one (t : ℕ) (E : Finset (H → ℕ))
    (π : H → ℝ) (hπ : ∀ h, 0 ≤ π h) (hπsum : (∑ h, π h) ≤ 1) :
    (∑ n ∈ E, (wordCount t n : ℝ) * ∏ h, π h ^ n h) ≤ 1 := by
  classical
  have hrestrict :
      (∑ n ∈ E ∩ wordProfiles H t, (wordCount t n : ℝ) * ∏ h, π h ^ n h) =
        ∑ n ∈ E, (wordCount t n : ℝ) * ∏ h, π h ^ n h := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hn hnot
    have hout : n ∉ wordProfiles H t := by
      intro hp
      exact hnot (Finset.mem_inter.mpr ⟨hn, hp⟩)
    rw [wordCount_eq_zero_of_not_mem_wordProfiles t n hout]
    simp only [Nat.cast_zero, zero_mul]
  rw [← hrestrict]
  calc
    _ ≤ ∑ n ∈ wordProfiles H t, (wordCount t n : ℝ) * ∏ h, π h ^ n h :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun n _ _ => wordCount_weight_nonneg t π hπ n)
    _ ≤ 1 := sum_wordCount_weight_le_one t π hπ hπsum

end TalagrandThreshold

end OAI
