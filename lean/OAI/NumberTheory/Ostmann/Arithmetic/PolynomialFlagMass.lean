import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementWeighted
import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialRootMass

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialFlagMass
open scoped BigOperators
open MvPolynomial ProductExpectation PolynomialFlagReplacement

theorem divisibility_probability_le {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (hP : P ≠ 0)
    (S : Fin n → Finset ℤ) (μ : Fin n → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H C Cnu : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hC : 0 ≤ C) (hCnu : 0 ≤ Cnu)
    (hμ : ∀i a,a∈S i → 0 ≤ μ i a) (hmass : ∀i,∑a∈S i,μ i a ≤ C)
    (hatom : ∀i a,a∈S i → μ i a ≤ α)
    (hprime : ∀b∈B,b.Prime) (hνmass : ∑b∈B,ν b ≤ Cnu)
    (hνatom : ∀b∈B,ν b ≤ β)
    (hsize : ∀x,(∀i,x i∈S i) → eval x P ≠ 0 → Real.log |((eval x P:ℤ):ℝ)| ≤ H) :
    expectation S μ (fun x => ∑b∈B,ν b*divisibilityIndicator P x b) ≤
      (P.totalDegree:ℝ)*α*C^(n-1)*Cnu+β*(H/Real.log 2)*C^n := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hfiber (x : Fin n → ℤ) (hx : ∀i,x i∈S i) :
      (∑b∈B,ν b*divisibilityIndicator P x b) ≤
        Cnu*(if eval x P=0 then 1 else 0)+β*(H/Real.log 2) := by
    by_cases hz : eval x P=0
    · simp only [divisibilityIndicator,hz,dvd_zero,ite_true,mul_one]
      exact hνmass.trans (le_add_of_nonneg_right (mul_nonneg hβ (div_nonneg hH hlog2.le)))
    · simp only [hz,ite_false,mul_zero,zero_add]
      have hN : (eval x P).natAbs ≠ 0 := by simpa only [Int.natAbs_ne_zero] using hz
      have hd := AccidentalDivisibility.weighted_prime_divisors (eval x P).natAbs hN B ν hβ hνatom
      have he : (∑b∈B,ν b*divisibilityIndicator P x b)=
          ∑b∈B with b.Prime ∧ b ∣ (eval x P).natAbs,ν b := by
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
    _ ≤ expectation S μ (fun x => Cnu*(if eval x P=0 then 1 else 0)+β*(H/Real.log 2)) :=
      expectation_mono_support S μ hμ hfiber
    _ = Cnu*expectation S μ (fun x => if eval x P=0 then 1 else 0)+
        expectation S μ (fun _ => β*(H/Real.log 2)) := by
      rw [ProductExpectation.add,expectation_const_mul]
    _ ≤ Cnu*((P.totalDegree:ℝ)*α*C^(n-1))+β*(H/Real.log 2)*C^n := add_le_add
      (mul_le_mul_of_nonneg_left
        (PolynomialRootMass.weighted_zero_bound P hP S μ α C hα hC hμ hmass hatom) hCnu)
      (PolynomialRootMass.expectation_const_le S μ hμ hmass (by positivity))
    _ = _ := by ring

theorem weighted_restricted_flag_error_le {n : ℕ} (P : MvPolynomial (Fin n) ℤ) (hP : P ≠ 0)
    (S : Fin n → Finset ℤ) (μ : Fin n → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A C Cnu : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hC : 0 ≤ C) (hCnu : 0 ≤ Cnu)
    (hμ : ∀i a,a∈S i → 0 ≤ μ i a) (hmass : ∀i,∑a∈S i,μ i a ≤ C)
    (hatom : ∀i a,a∈S i → μ i a ≤ α)
    (hprime : ∀b∈B,b.Prime) (hν : ∀b∈B,0 ≤ ν b) (hνmass : ∑b∈B,ν b ≤ Cnu)
    (hνatom : ∀b∈B,ν b ≤ β)
    (hsize : ∀x,(∀i,x i∈S i) → eval x P ≠ 0 → Real.log |((eval x P:ℤ):ℝ)| ≤ H)
    (r : (Fin n → ℤ) → ℕ → Bool) (w : (Fin n → ℤ) → ℕ → ℝ)
    (hw : ∀x,(∀i,x i∈S i) → ∀b∈B,0 ≤ w x b ∧ w x b ≤ A) :
    expectation S μ (fun x => ∑b∈B,ν b*(if r x b then w x b*flagError P x b else 0)) ≤
      A*((P.totalDegree:ℝ)*α*C^(n-1)*Cnu+β*(H/Real.log 2)*C^n) := by
  have he : expectation S μ (fun x => ∑b∈B,ν b*(if r x b then w x b*flagError P x b else 0)) ≤
      expectation S μ (fun x => A*(∑b∈B,ν b*divisibilityIndicator P x b)) := by
    apply expectation_mono_support S μ hμ
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hp : (if r x b then w x b*flagError P x b else 0) ≤ A*divisibilityIndicator P x b := by
      rw [flagError_of_ne_zero P hP]
      split_ifs
      · exact mul_le_mul_of_nonneg_right (hw x hx b hb).2 (indicator_nonneg P x b)
      · exact mul_nonneg hA (indicator_nonneg P x b)
    have hh := mul_le_mul_of_nonneg_left hp (hν b hb)
    simpa only [mul_assoc,mul_left_comm] using hh
  rw [expectation_const_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left
    (divisibility_probability_le P hP S μ B ν α β H C Cnu hα hβ hH hC hCnu hμ hmass hatom
      hprime hνmass hνatom hsize) hA)

end Ostmann.Arithmetic.PolynomialFlagMass

end

end OAI
