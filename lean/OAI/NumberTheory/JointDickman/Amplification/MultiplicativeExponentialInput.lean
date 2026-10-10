import OAI.NumberTheory.JointDickman.Counting.OscillatoryCoefficientLaw

namespace OAI

/-! # The published multiplicative exponential-sum input

Montgomery--Vaughan, *Exponential sums with multiplicative coefficients*,
Invent. Math. 43 (1977), Corollary 1, DOI 10.1007/BF01390204.
We need only real, everywhere 1-bounded multiplicative coefficients.
These satisfy both hypotheses of the published theorem: the prime bound
and the sum of squares bound. The uniform constant is independent of the
coefficient, hence also of the moving finite set of excluded primes.
-/

namespace JointDickman
open Finset ArithmeticFunction

namespace PublishedInputs

/-- The finite partial-sum specialization of Montgomery--Vaughan Cor. 1. -/
def MultiplicativeExponentialInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ f : ArithmeticFunction ℝ, f.IsMultiplicative →
    (∀ n, |f n| ≤ 1) → ∀ (Y q : ℕ) (u : ℤ) (θ R : ℝ),
    2 ≤ Y → 0 < q → Nat.Coprime u.natAbs q →
    |θ-(u : ℝ)/q| ≤ 1/(q : ℝ)^2 →
    2 ≤ R → R ≤ q → (q : ℝ) ≤ Y/R →
    ‖∑ n ∈ Icc 1 Y, (f n : ℂ)*additivePhase ((n : ℝ)*θ)‖ ≤
      C*((Y : ℝ)/Real.log Y + Y*(Real.log R)^(3/2 : ℝ)/Real.sqrt R)

end PublishedInputs

theorem roughSquarefreeWeight_half_bounded (E : Finset ℕ) (n : ℕ) :
    |roughSquarefreeWeight E (1/2) n| ≤ 1 := by
  simp only [roughSquarefreeWeight,squarefreeWeight,coe_mk]
  split_ifs <;> first
    | exact (abs_of_nonneg (by positivity)).trans_le
        (pow_le_one₀ (by norm_num) (by norm_num))
    | norm_num

theorem roughSquarefreeWeight_half_square_sum (E : Finset ℕ) (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, (roughSquarefreeWeight E (1/2) n)^2) ≤ Y := by
  calc
    _ ≤ ∑ _n ∈ Icc 1 Y, (1 : ℝ) := by
      apply sum_le_sum
      intro n _
      have h := roughSquarefreeWeight_half_bounded E n
      simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr h
    _ = _ := by simp

theorem rough_exponential_partial_sum_bound
    (hMV : PublishedInputs.MultiplicativeExponentialInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset ℕ) (Y q : ℕ) (u : ℤ) (θ R : ℝ),
    2 ≤ Y → 0 < q → Nat.Coprime u.natAbs q →
    |θ-(u : ℝ)/q| ≤ 1/(q : ℝ)^2 →
    2 ≤ R → R ≤ q → (q : ℝ) ≤ Y/R →
    ‖∑ n ∈ Icc 1 Y, (roughSquarefreeWeight E (1/2) n : ℂ)*additivePhase ((n : ℝ)*θ)‖ ≤
      C*((Y : ℝ)/Real.log Y + Y*(Real.log R)^(3/2 : ℝ)/Real.sqrt R) := by
  obtain ⟨C,hC,hbound⟩ := hMV
  exact ⟨C,hC,fun E => hbound (roughSquarefreeWeight E (1/2))
    (roughSquarefreeWeight_isMultiplicative E (1/2)) (roughSquarefreeWeight_half_bounded E)⟩

end JointDickman

end OAI
