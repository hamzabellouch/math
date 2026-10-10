import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementExpectation

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialFlagReplacement
open scoped BigOperators
open MvPolynomial ProductExpectation

def divisibilityIndicator {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (x : Fin n → ℤ) (b : ℕ) : ℝ :=
  if (b:ℤ) ∣ eval x P then 1 else 0

def flagError {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (x : Fin n → ℤ) (b : ℕ) : ℝ :=
  |divisibilityIndicator P x b - if P=0 then 1 else 0|

@[simp] theorem zero_polynomial_flag {n : ℕ} (x : Fin n → ℤ) (b : ℕ) :
    divisibilityIndicator (0 : MvPolynomial (Fin n) ℤ) x b=1 := by
  simp [divisibilityIndicator]

@[simp] theorem zero_polynomial_error {n : ℕ} (x : Fin n → ℤ) (b : ℕ) :
    flagError (0 : MvPolynomial (Fin n) ℤ) x b=0 := by simp [flagError]

lemma indicator_nonneg {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (x : Fin n → ℤ) (b : ℕ) :
    0 ≤ divisibilityIndicator P x b := by unfold divisibilityIndicator; split_ifs <;> norm_num

lemma flagError_of_ne_zero {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (hP : P≠0)
    (x : Fin n → ℤ) (b : ℕ) : flagError P x b=divisibilityIndicator P x b := by
  simp only [flagError,hP,ite_false,sub_zero,abs_of_nonneg (indicator_nonneg P x b)]

theorem divisibility_probability_le {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (hP : P≠0)
    (S : Fin n → Finset ℤ) (μ : Fin n → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H : ℝ) (hα : 0≤α) (hβ : 0≤β) (hH : 0≤H)
    (hμ : ∀ i a, a∈S i → 0≤μ i a) (hmass : ∀ i, ∑ a∈S i, μ i a=1)
    (hatom : ∀ i a, a∈S i → μ i a≤α)
    (hprime : ∀ b∈B, b.Prime) (hνmass : ∑ b∈B,ν b=1)
    (hνatom : ∀ b∈B,ν b≤β)
    (hsize : ∀ x, (∀ i,x i∈S i) → eval x P≠0 → Real.log |((eval x P:ℤ):ℝ)|≤H) :
    expectation S μ (fun x => ∑ b∈B,ν b*divisibilityIndicator P x b) ≤
      (P.totalDegree:ℝ)*α + β*(H/Real.log 2) := by
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hfiber : ∀ x, (∀ i,x i∈S i) →
      (∑ b∈B,ν b*divisibilityIndicator P x b) ≤
        (if eval x P=0 then 1 else 0) + β*(H/Real.log 2) := by
    intro x hx
    by_cases hz : eval x P=0
    · simp only [divisibilityIndicator,hz,dvd_zero,ite_true,mul_one,hνmass]
      exact le_add_of_nonneg_right (mul_nonneg hβ (div_nonneg hH hlog2.le))
    · rw [ite_eq_right hz,zero_add]
      have hN : (eval x P).natAbs≠0 := by simpa only [Int.natAbs_ne_zero] using hz
      have hd := AccidentalDivisibility.weighted_prime_divisors (eval x P).natAbs hN B ν hβ hνatom
      have he : (∑ b∈B,ν b*divisibilityIndicator P x b) =
          ∑ b∈B with b.Prime ∧ b ∣ (eval x P).natAbs,ν b := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro b hb
        simp only [divisibilityIndicator,Int.natCast_dvd,hprime b hb,true_and]
        split_ifs <;> simp
      rw [he]
      apply hd.trans
      apply mul_le_mul_of_nonneg_left _ hβ
      apply div_le_div_of_nonneg_right _ hlog2.le
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hsize x hx hz
  calc
    _ ≤ expectation S μ (fun x => (if eval x P=0 then 1 else 0)+β*(H/Real.log 2)) :=
      expectation_mono_support S μ hμ hfiber
    _ = expectation S μ (fun x => if eval x P=0 then 1 else 0)+β*(H/Real.log 2) := by
      rw [ProductExpectation.add,ProductExpectation.const S μ hmass]
    _ ≤ _ := add_le_add (PolynomialRootProbability.weighted_zero_bound P hP S μ α hα hμ hmass hatom) le_rfl

theorem identity_replacement_exact {n : ℕ} (S : Fin n → Finset ℤ) (μ : Fin n → ℤ → ℝ)
    (B : Finset ℕ) (ν : ℕ → ℝ) :
    expectation S μ (fun x => ∑ b∈B,ν b*flagError (0 : MvPolynomial (Fin n) ℤ) x b)=0 := by
  simp only [zero_polynomial_error,mul_zero,Finset.sum_const_zero,expectation_zero]

end Ostmann.Arithmetic.PolynomialFlagReplacement

end

end OAI
