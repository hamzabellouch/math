import OAI.Combinatorics.ProgressionColoring.CoshBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

universe uLabel

namespace QuantitativeVanDerWaerden
namespace FairBitTail

open scoped BigOperators

variable {Label : Type uLabel} [Fintype Label] [DecidableEq Label]

/-- Each independent fair-bit assignment has this product weight. -/
def weight (_ω : Label → Bool) : ℝ := ∏ _i : Label, (1 / 2 : ℝ)

theorem weight_nonneg {Label : Type uLabel} [Fintype Label] [DecidableEq Label]
    (ω : Label → Bool) : 0 ≤ weight ω := by
  unfold weight
  exact Finset.prod_nonneg (fun _ _ => by norm_num)

/-- The centered deficit contributed by one bit. -/
def deviation (b x : Bool) : ℝ := if x = b then -(1 / 2 : ℝ) else 1 / 2

theorem sum_deviation {Label : Type uLabel} [Fintype Label] [DecidableEq Label]
    (S : Finset Label) (b : Bool) (ω : Label → Bool) :
    (∑ i ∈ S, deviation b (ω i)) =
      (S.card : ℝ) / 2 - ((S.filter fun i => ω i = b).card : ℝ) := by
  classical
  calc
    (∑ i ∈ S, deviation b (ω i)) =
        ∑ i ∈ S, ((1 / 2 : ℝ) - if ω i = b then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold deviation
      split_ifs <;> norm_num
    _ = (S.card : ℝ) / 2 - ((S.filter fun i => ω i = b).card : ℝ) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_boole]
      ring

/-- The exact moment generating function on any distinct label support. -/
theorem exponential_moment (S : Finset Label) (b : Bool) :
    (∑ ω : Label → Bool, weight ω *
      Real.exp (∑ i ∈ S, deviation b (ω i))) =
        Real.cosh (1 / 2 : ℝ) ^ S.card := by
  classical
  calc
    (∑ ω : Label → Bool, weight ω *
        Real.exp (∑ i ∈ S, deviation b (ω i))) =
        ∑ ω : Label → Bool, ∏ i : Label,
          ((1 / 2 : ℝ) * if i ∈ S then Real.exp (deviation b (ω i)) else 1) := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem, Real.exp_sum]
      rfl
    _ = ∏ i : Label, ∑ x : Bool,
          ((1 / 2 : ℝ) * if i ∈ S then Real.exp (deviation b x) else 1) := by
      exact (Fintype.prod_sum (fun (i : Label) (x : Bool) =>
        (1 / 2 : ℝ) * if i ∈ S then Real.exp (deviation b x) else 1)).symm
    _ = ∏ i : Label, if i ∈ S then Real.cosh (1 / 2 : ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ S
      · cases b <;> simp [hi, deviation, Real.cosh_eq] <;> ring
      · simp [hi]
    _ = Real.cosh (1 / 2 : ℝ) ^ S.card := by simp

theorem exponential_moment_le (S : Finset Label) (b : Bool) :
    (∑ ω : Label → Bool, weight ω *
      Real.exp (∑ i ∈ S, deviation b (ω i))) ≤ Real.exp ((S.card : ℝ) / 8) := by
  rw [exponential_moment]
  calc
    Real.cosh (1 / 2 : ℝ) ^ S.card ≤ Real.exp (1 / 8 : ℝ) ^ S.card :=
      pow_le_pow_left₀ (Real.cosh_pos _).le cosh_half_le_exp_eighth _
    _ = Real.exp ((S.card : ℝ) / 8) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Exponential Markov for the lower tail of either selected bit. -/
theorem one_bit_tail (S : Finset Label) (b : Bool) :
    (∑ ω : Label → Bool,
      if 4 * (S.filter fun i => ω i = b).card < S.card then weight ω else 0) ≤
        Real.exp (-(S.card : ℝ) / 8) := by
  classical
  have hp (ω : Label → Bool) :
      (if 4 * (S.filter fun i => ω i = b).card < S.card then weight ω else 0) ≤
        weight ω * Real.exp (∑ i ∈ S, deviation b (ω i)) /
          Real.exp ((S.card : ℝ) / 4) := by
    by_cases hω : 4 * (S.filter fun i => ω i = b).card < S.card
    · rw [ite_eq_left hω]
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg ω)
      apply Real.exp_le_exp.mpr
      rw [sum_deviation]
      have hc : (4 : ℝ) * ((S.filter fun i => ω i = b).card : ℝ) <
          (S.card : ℝ) := by exact_mod_cast hω
      linarith
    · rw [ite_eq_right hω]
      exact div_nonneg (mul_nonneg (weight_nonneg ω) (Real.exp_pos _).le)
        (Real.exp_pos _).le
  calc
    (∑ ω : Label → Bool,
        if 4 * (S.filter fun i => ω i = b).card < S.card then weight ω else 0) ≤
        ∑ ω : Label → Bool,
          weight ω * Real.exp (∑ i ∈ S, deviation b (ω i)) /
            Real.exp ((S.card : ℝ) / 4) := Finset.sum_le_sum (fun ω _ => hp ω)
    _ = (∑ ω : Label → Bool, weight ω *
          Real.exp (∑ i ∈ S, deviation b (ω i))) / Real.exp ((S.card : ℝ) / 4) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ Real.exp ((S.card : ℝ) / 8) / Real.exp ((S.card : ℝ) / 4) :=
      div_le_div_of_nonneg_right (exponential_moment_le S b) (Real.exp_pos _).le
    _ = Real.exp (-(S.card : ℝ) / 8) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- Some bit has fewer than a quarter of the tested labels with probability
at most `2 exp(-|S|/8)`. The empty support is included. -/
theorem balancing_tail (S : Finset Label) :
    (∑ ω : Label → Bool,
      if ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card
      then weight ω else 0) ≤ 2 * Real.exp (-(S.card : ℝ) / 8) := by
  classical
  have hu (ω : Label → Bool) :
      (if ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card
        then weight ω else 0) ≤
      (if 4 * (S.filter fun i => ω i = false).card < S.card then weight ω else 0) +
      (if 4 * (S.filter fun i => ω i = true).card < S.card then weight ω else 0) := by
    by_cases hf : 4 * (S.filter fun i => ω i = false).card < S.card
    · have he : ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card := ⟨false, hf⟩
      simp only [ite_eq_left he, ite_eq_left hf]
      apply le_add_of_nonneg_right
      split_ifs
      · exact weight_nonneg ω
      · exact le_rfl
    · by_cases ht : 4 * (S.filter fun i => ω i = true).card < S.card
      · have he : ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card := ⟨true, ht⟩
        simp [he, hf, ht]
      · have he : ¬ ∃ b : Bool, 4 * (S.filter fun i => ω i = b).card < S.card := by
          rintro ⟨b, hb⟩
          cases b
          · exact hf hb
          · exact ht hb
        simp [he, hf, ht]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hu ω)
  rw [Finset.sum_add_distrib] at hsum
  have hfalse := one_bit_tail S false
  have htrue := one_bit_tail S true
  linarith

end FairBitTail
end QuantitativeVanDerWaerden

end

end OAI
