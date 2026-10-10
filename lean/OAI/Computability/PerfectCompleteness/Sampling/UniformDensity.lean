import OAI.Computability.PerfectCompleteness.Foundations.RecursiveSpaceEquivLemmas
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas

namespace OAI

section

namespace PerfectCompleteness.UniformDensity

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def density (μ : FiniteDistribution Ω) (x : Ω) : ℝ :=
  (Fintype.card Ω : ℝ) * μ.weight x

theorem weight_eq (μ : FiniteDistribution Ω) (x : Ω) :
    μ.weight x = (FiniteDistribution.uniform Ω).weight x * density μ x := by
  have hn : (Fintype.card Ω : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change μ.weight x = (1 / (Fintype.card Ω : ℝ)) *
    ((Fintype.card Ω : ℝ) * μ.weight x)
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hn, one_mul]

theorem mean_one (μ : FiniteDistribution Ω) :
    (FiniteDistribution.uniform Ω).expectation (density μ) = 1 := by
  change (∑ x, (FiniteDistribution.uniform Ω).weight x * density μ x) = 1
  simp_rw [← weight_eq μ]
  exact μ.normalized

omit [Nonempty Ω] in
theorem nonnegative (μ : FiniteDistribution Ω) (x : Ω) :
    0 ≤ density μ x :=
  mul_nonneg (Nat.cast_nonneg _) (μ.nonnegative x)

omit [Nonempty Ω] in
private theorem weight_le_one (μ : FiniteDistribution Ω) (x : Ω) :
    μ.weight x ≤ 1 := by
  classical
  calc
    μ.weight x ≤ ∑ y, μ.weight y :=
      Finset.single_le_sum (fun y _ => μ.nonnegative y) (Finset.mem_univ x)
    _ = 1 := μ.normalized

omit [Nonempty Ω] in
theorem density_le_card (μ : FiniteDistribution Ω) (x : Ω) :
    density μ x ≤ (Fintype.card Ω : ℝ) := by
  simpa only [density, mul_one] using
    mul_le_mul_of_nonneg_left (weight_le_one μ x) (Nat.cast_nonneg (Fintype.card Ω) :
      (0 : ℝ) ≤ (Fintype.card Ω : ℝ))

theorem second_moment_le_card_sub_one (μ : FiniteDistribution Ω) :
    (FiniteDistribution.uniform Ω).expectation (fun x => (density μ x - 1) ^ 2) ≤
      (Fintype.card Ω : ℝ) - 1 := by
  have hpoint (x : Ω) :
      (density μ x - 1) ^ 2 ≤ ((Fintype.card Ω : ℝ) - 2) * density μ x + 1 := by
    have hmul := mul_le_mul_of_nonneg_right (density_le_card μ x) (nonnegative μ x)
    nlinarith
  have hexpectation :
      (FiniteDistribution.uniform Ω).expectation
          (fun x => ((Fintype.card Ω : ℝ) - 2) * density μ x + 1) =
        ((Fintype.card Ω : ℝ) - 2) *
          (FiniteDistribution.uniform Ω).expectation (density μ) + 1 := by
    unfold FiniteDistribution.expectation
    rw [Finset.mul_sum]
    simp only [mul_add, mul_one, Finset.sum_add_distrib]
    rw [(FiniteDistribution.uniform Ω).normalized]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    ring
  calc
    _ ≤ (FiniteDistribution.uniform Ω).expectation
        (fun x => ((Fintype.card Ω : ℝ) - 2) * density μ x + 1) :=
      SmallBias.expectation_mono (FiniteDistribution.uniform Ω) hpoint
    _ = ((Fintype.card Ω : ℝ) - 2) *
        (FiniteDistribution.uniform Ω).expectation (density μ) + 1 := hexpectation
    _ = (Fintype.card Ω : ℝ) - 1 := by rw [mean_one]; ring

theorem second_moment_le (μ : FiniteDistribution Ω) (L : ℝ)
    (hcard : (Fintype.card Ω : ℝ) ≤ L) :
    (FiniteDistribution.uniform Ω).expectation (fun x => (density μ x - 1) ^ 2) ≤
      L ^ 2 := by
  apply (second_moment_le_card_sub_one μ).trans
  have hL : 0 ≤ L := (Nat.cast_nonneg (Fintype.card Ω)).trans hcard
  nlinarith [sq_nonneg (L - 1)]

end
end PerfectCompleteness.UniformDensity

end

end OAI
