import OAI.NumberTheory.Ostmann.Supply.CompletionArithmetic

namespace OAI

namespace Ostmann.Supply.CompletionCounting
open Finset

def primesUpTo (U : ℕ) : Finset ℕ := (Icc 2 U).filter Nat.Prime

def primeCost (w : ℕ → ℝ) (u : ℕ) : ℝ := ∑ p ∈ u.primeFactors, w p

noncomputable def goodCompletions (U t : ℕ) (w : ℕ → ℝ) (B : ℝ) : Finset ℕ :=
  (Icc 1 U).filter (fun u => Squarefree u ∧ Nat.Coprime u t ∧ primeCost w u ≤ B)

theorem primeFactors_eq_filter {U u : ℕ} (hu : u ∈ Icc 1 U) :
    u.primeFactors = (primesUpTo U).filter (fun p => p ∣ u) := by
  ext p
  constructor
  · intro hp
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
        (Nat.le_of_mem_primeFactors hp).trans (mem_Icc.mp hu).2⟩,
        Nat.prime_of_mem_primeFactors hp⟩, Nat.dvd_of_mem_primeFactors hp⟩
  · intro hp
    obtain ⟨hp, hpu⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp).2, hpu,
      by have := (mem_Icc.mp hu).1; omega⟩

theorem sum_primeCost (U : ℕ) (w : ℕ → ℝ) :
    ∑ u ∈ Icc 1 U, primeCost w u =
      ∑ p ∈ primesUpTo U, ((multiplesUpTo U p).card : ℝ) * w p := by
  calc
    _ = ∑ u ∈ Icc 1 U, ∑ p ∈ primesUpTo U, if p ∣ u then w p else 0 := by
      apply sum_congr rfl
      intro u hu
      rw [primeCost, primeFactors_eq_filter hu, sum_filter]
    _ = ∑ p ∈ primesUpTo U, ∑ u ∈ Icc 1 U, if p ∣ u then w p else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      rw [← sum_filter]
      simp [multiplesUpTo]

theorem sum_primeCost_le (U : ℕ) (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p) :
    ∑ u ∈ Icc 1 U, primeCost w u ≤
      (U : ℝ) * ∑ p ∈ primesUpTo U, w p / p := by
  rw [sum_primeCost, mul_sum]
  apply sum_le_sum
  intro p hp
  calc
    _ ≤ ((U : ℝ) / p) * w p :=
      mul_le_mul_of_nonneg_right (card_multiplesUpTo_le U p) (hw p)
    _ = _ := by ring

theorem card_large_primeCost_le (U : ℕ) (w : ℕ → ℝ) (hw : ∀ p, 0 ≤ w p)
    {B : ℝ} (hB : 0 < B)
    (hmean : ∑ p ∈ primesUpTo U, w p / p ≤ B / 16) :
    (((Icc 1 U).filter (fun u => B < primeCost w u)).card : ℝ) ≤ (U : ℝ) / 16 := by
  let bad := (Icc 1 U).filter (fun u => B < primeCost w u)
  have hsum : B * (bad.card : ℝ) ≤ ∑ u ∈ Icc 1 U, primeCost w u := by
    calc
      _ = ∑ u ∈ bad, B := by simp [mul_comm]
      _ ≤ ∑ u ∈ bad, primeCost w u :=
        sum_le_sum (fun u hu => le_of_lt (mem_filter.mp hu).2)
      _ ≤ ∑ u ∈ Icc 1 U, primeCost w u := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro u hu hbad
        exact sum_nonneg (fun p hp => hw p)
  have hmoment := sum_primeCost_le U w hw
  have hbound := mul_le_mul_of_nonneg_left hmean (show (0 : ℝ) ≤ U by positivity)
  change (bad.card : ℝ) ≤ _
  nlinarith

theorem card_goodCompletions_ge (U t : ℕ) (ht : t ≠ 0) (w : ℕ → ℝ)
    (hw : ∀ p, 0 ≤ w p) {B : ℝ} (hB : 0 < B)
    (hcop : ∑ p ∈ t.primeFactors, (1 : ℝ) / p ≤ 1 / 16)
    (hmean : ∑ p ∈ primesUpTo U, w p / p ≤ B / 16) :
    (U : ℝ) / 8 ≤ ((goodCompletions U t w B).card : ℝ) := by
  classical
  let badSq := (Icc 1 U).filter (fun u => ¬Squarefree u)
  let badCop := (Icc 1 U).filter (fun u => ¬Nat.Coprime u t)
  let badCost := (Icc 1 U).filter (fun u => B < primeCost w u)
  have hcover : Icc 1 U ⊆ ((goodCompletions U t w B ∪ badSq) ∪ badCop) ∪ badCost := by
    intro u hu
    by_cases hs : Squarefree u
    · by_cases hc : Nat.Coprime u t
      · by_cases hwB : primeCost w u ≤ B
        · exact mem_union_left _ (mem_union_left _ (mem_union_left _
            (mem_filter.mpr ⟨hu, hs, hc, hwB⟩)))
        · exact mem_union_right _ (mem_filter.mpr ⟨hu, lt_of_not_ge hwB⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hu, hc⟩))
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hu, hs⟩)))
  have hcount : (Icc 1 U).card ≤ (goodCompletions U t w B).card +
      badSq.card + badCop.card + badCost.card := by
    exact (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _)) _))
  have hcountR : (U : ℝ) ≤ ((goodCompletions U t w B).card : ℝ) +
      (badSq.card : ℝ) + (badCop.card : ℝ) + (badCost.card : ℝ) := by
    exact_mod_cast (show U ≤ _ by simpa using hcount)
  have hsq := card_nonsquarefree_le U
  have hcp := (card_noncoprime_le U t ht).trans
    (mul_le_mul_of_nonneg_left hcop (show (0 : ℝ) ≤ U by positivity))
  have hcs := card_large_primeCost_le U w hw hB hmean
  change (badSq.card : ℝ) ≤ _ at hsq
  change (badCop.card : ℝ) ≤ _ at hcp
  change (badCost.card : ℝ) ≤ _ at hcs
  linarith

end Ostmann.Supply.CompletionCounting

end OAI
