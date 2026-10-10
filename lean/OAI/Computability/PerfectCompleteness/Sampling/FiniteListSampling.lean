import Mathlib.Algebra.BigOperators.Field
import OAI.Computability.PerfectCompleteness.Foundations.OccurrenceStochasticLemmas

namespace OAI

section

namespace PerfectCompleteness.FiniteListSampling

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def uniformList (L : Finset A) (nonempty : L.Nonempty) : FiniteDistribution A where
  weight a := if a ∈ L then 1 / (L.card : ℝ) else 0
  nonnegative a := by
    split
    · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  normalized := by
    have hcard : (L.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt nonempty.card_pos)
    simp only [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact div_self hcard

@[simp] theorem uniformList_weight_mem (L : Finset A) (hne : L.Nonempty)
    (a : A) (ha : a ∈ L) : (uniformList L hne).weight a = 1 / (L.card : ℝ) := by
  simp [uniformList, ha]

omit [DecidableEq A] in
theorem probability_ge_weight (μ : FiniteDistribution A) (event : A → Bool)
    (a : A) (ha : event a = true) : μ.weight a ≤ μ.probability event := by
  change μ.weight a ≤ ∑ x, if event x then μ.weight x else 0
  have h := Finset.single_le_sum
    (f := fun x : A => if event x then μ.weight x else 0)
    (fun x _ => by split; exact μ.nonnegative x; exact le_rfl) (Finset.mem_univ a)
  simpa only [ha, ite_true] using h

def pairAcceptance (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (accepts : A → B → Bool) : ℝ :=
  μ.expectation (fun a => ν.probability (accepts a))

omit [DecidableEq A] [DecidableEq B] in
theorem pairAcceptance_nonnegative (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (accepts : A → B → Bool) : 0 ≤ pairAcceptance μ ν accepts := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (μ.nonnegative a) (ν.probability_nonnegative _)

omit [DecidableEq A] [DecidableEq B] in
theorem pair_weight_le_acceptance (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (accepts : A → B → Bool) (a : A) (b : B) (accepted : accepts a b = true) :
    μ.weight a * ν.weight b ≤ pairAcceptance μ ν accepts := by
  have hinner := probability_ge_weight ν (accepts a) b accepted
  calc
    _ ≤ μ.weight a * ν.probability (accepts a) :=
      mul_le_mul_of_nonneg_left hinner (μ.nonnegative a)
    _ ≤ _ := Finset.single_le_sum
      (fun x _ => mul_nonneg (μ.nonnegative x) (ν.probability_nonnegative _))
      (Finset.mem_univ a)

theorem uniform_pair_lower (L : Finset A) (R : Finset B)
    (hL : L.Nonempty) (hR : R.Nonempty) (accepts : A → B → Bool)
    (witness : ∃ a ∈ L, ∃ b ∈ R, accepts a b = true) :
    1 / ((L.card : ℝ) * (R.card : ℝ)) ≤
      pairAcceptance (uniformList L hL) (uniformList R hR) accepts := by
  obtain ⟨a, ha, b, hb, hab⟩ := witness
  have h := pair_weight_le_acceptance (uniformList L hL) (uniformList R hR) accepts a b hab
  simpa only [uniformList_weight_mem L hL a ha, uniformList_weight_mem R hR b hb,
    ← one_div_mul_one_div] using h

theorem bounded_uniform_pair_lower (L : Finset A) (R : Finset B)
    (hL : L.Nonempty) (hR : R.Nonempty) (s : Nat)
    (hLs : L.card ≤ s) (hRs : R.card ≤ s) (accepts : A → B → Bool)
    (witness : ∃ a ∈ L, ∃ b ∈ R, accepts a b = true) :
    1 / (s : ℝ) ^ 2 ≤
      pairAcceptance (uniformList L hL) (uniformList R hR) accepts := by
  have hLc : 0 < (L.card : ℝ) := Nat.cast_pos.mpr hL.card_pos
  have hRc : 0 < (R.card : ℝ) := Nat.cast_pos.mpr hR.card_pos
  have hLs' : (L.card : ℝ) ≤ s := by exact_mod_cast hLs
  have hRs' : (R.card : ℝ) ≤ s := by exact_mod_cast hRs
  have hprod : (L.card : ℝ) * (R.card : ℝ) ≤ (s : ℝ) ^ 2 := by
    simpa only [pow_two] using
      mul_le_mul hLs' hRs' (Nat.cast_nonneg R.card) (Nat.cast_nonneg s)
  exact (one_div_le_one_div_of_le (mul_pos hLc hRc) hprod).trans
    (uniform_pair_lower L R hL hR accepts witness)

omit [DecidableEq A] [DecidableEq B] in
theorem pairAcceptance_eq_expectation (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (accepts : A → B → Bool) :
    pairAcceptance μ ν accepts = μ.expectation
      (fun a => ν.expectation (fun b => if accepts a b then 1 else 0)) := by
  unfold pairAcceptance
  apply FiniteDistribution.expectation_congr
  intro a
  simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]

end
end PerfectCompleteness.FiniteListSampling

end

end OAI
