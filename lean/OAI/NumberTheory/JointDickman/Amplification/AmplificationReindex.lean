import OAI.NumberTheory.JointDickman.Arithmetic.DivisorReindex

namespace OAI

/-! # Reindexing the actual arithmetic amplification into a divisor form -/

namespace JointDickman
open Finset

noncomputable def arithmeticResidueWeight (B L : ℕ) (τ C : ℝ) (n : ℕ) : ℝ :=
  regularResidueWeight B L τ C (coefficientPrimeSet B n)

open Classical in
noncomputable def amplificationDivisorForm (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (H : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset, ∑ D ∈ (auxiliaryPrimes B).powerset,
    let a := ∏ p ∈ A, p
    let c := ∏ p ∈ D, p
    ∑ m ∈ range N, if a*m < N ∧ c ∣ a*m+1 then
      H (a*m) * (((regularCoefficientWeight B L τ C a * arithmeticResidueWeight B L τ C m) *
        (regularCoefficientWeight B L τ C c * arithmeticResidueWeight B L τ C ((a*m+1)/c)) *
        w a c : ℝ) : ℂ) else 0

theorem sum_two_divisors_reindex {a c : ℕ} (ha : 0 < a) (N : ℕ)
    (H : ℕ → ℂ) (F : ℕ → ℕ → ℂ) :
    (∑ n ∈ range N, if a ∣ n ∧ c ∣ n+1 then H n * F (n/a) ((n+1)/c) else 0) =
      ∑ m ∈ range N, if a*m < N ∧ c ∣ a*m+1 then H (a*m) * F m ((a*m+1)/c) else 0 := by
  classical
  have h := sum_dvd_ite_reindex ha N
    (fun n => if c ∣ n+1 then H n * F (n/a) ((n+1)/c) else 0)
  simpa only [ite_and, Nat.mul_div_cancel_left _ ha, ite_self] using h

/-- The finite first-form identity, including the precise endpoint. -/
theorem arithmeticAmplification_reindex (B L : ℕ) (τ C : ℝ)
    (w : ℕ → ℕ → ℝ) (H : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range N, H n * (arithmeticSubsetAmplification B L τ C w n : ℂ)) =
      (1 / (B : ℂ)) * amplificationDivisorForm B L τ C w H N := by
  classical
  let F (n : ℕ) (A D : Finset ℕ) : ℂ :=
    if (∏ p ∈ A, p) ∣ n ∧ (∏ p ∈ D, p) ∣ n+1 then
      H n * (((regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
        arithmeticResidueWeight B L τ C (n/(∏ p ∈ A, p))) *
        (regularCoefficientWeight B L τ C (∏ p ∈ D, p) *
          arithmeticResidueWeight B L τ C ((n+1)/(∏ p ∈ D, p))) *
        w (∏ p ∈ A, p) (∏ p ∈ D, p) : ℝ) : ℂ) else 0
  have he (n : ℕ) : H n * (arithmeticSubsetAmplification B L τ C w n : ℂ) =
      (1 / (B : ℂ)) * ∑ A ∈ (auxiliaryPrimes B).powerset,
        ∑ D ∈ (auxiliaryPrimes B).powerset, F n A D := by
    unfold arithmeticSubsetAmplification
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_natCast, Complex.ofReal_sum]
    rw [mul_left_comm, mul_sum]
    congr 1
    apply sum_congr rfl
    intro A _
    rw [mul_sum]
    apply sum_congr rfl
    intro D _
    dsimp only [F, arithmeticResidueWeight]
    split_ifs <;> simp only [Complex.ofReal_mul, Complex.ofReal_zero, mul_zero]
  simp_rw [he]
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  unfold amplificationDivisorForm
  apply sum_congr rfl
  intro A hA
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  have ha : 0 < ∏ p ∈ A, p := prod_pos (fun p hp =>
    (auxiliaryPrimes_prime B p (mem_powerset.mp hA hp)).pos)
  exact sum_two_divisors_reindex ha N H
    (fun m l => (((regularCoefficientWeight B L τ C (∏ p ∈ A, p) *
      arithmeticResidueWeight B L τ C m) *
      (regularCoefficientWeight B L τ C (∏ p ∈ D, p) * arithmeticResidueWeight B L τ C l) *
      w (∏ p ∈ A, p) (∏ p ∈ D, p) : ℝ) : ℂ))

end JointDickman

end OAI
