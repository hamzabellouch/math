import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientEnergy
import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientExpansion

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem kernelCoefficient_character_sum_lower_of_error_budget {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hJ : 0 < P.card)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) (u : ℤ)
    {c : ℝ} (hc : 0 ≤ c)
    (hmean : c ≤ |signAverage P (fun p => ε p*jacobiSym u p)|)
    (hbudget : (((k : ℝ)+1)*(k : ℝ)^2/P.card) *
      (|signAverage P (fun p => ε p*jacobiSym u p)|+
        (k : ℝ)/Real.sqrt (P.card : ℝ))^(k-2) ≤ c^k/2) :
    c^k/2 ≤ ‖∑ s ∈ primeProductSamples P k,
      kernelCoefficient P ε k s*(jacobiSym u s : ℂ)‖ := by
  have hy : ∀ p ∈ P, ε p*jacobiSym u p = -1 ∨ ε p*jacobiSym u p = 0 ∨ ε p*jacobiSym u p = 1 :=
    fun p hp => oriented_jacobi_trichotomy (ε p) u p (hε p hp)
  have he := (distinctSignAverage_error P hJ (fun p => ε p*jacobiSym u p) hy hk heven).trans hbudget
  have hpow : c^k ≤ signAverage P (fun p => ε p*jacobiSym u p)^k := by
    exact (pow_le_pow_left₀ hc hmean k).trans_eq (heven.pow_abs _)
  rw [kernelCoefficient_character_sum hP, Complex.norm_real, Real.norm_eq_abs]
  have hlow := (abs_le.mp he).1
  have hnorm := le_abs_self (distinctSignAverage P (fun p => ε p*jacobiSym u p) k)
  linarith

theorem kernelCoefficient_character_sum_lower {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (hJ : 0 < P.card)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) (u : ℤ)
    {c : ℝ} (hc : 0 ≤ c)
    (hmean : c ≤ |signAverage P (fun p => ε p*jacobiSym u p)|)
    (hbudget : (((k : ℝ)+1)*(k : ℝ)^2/P.card) *
      (1+(k : ℝ)/Real.sqrt (P.card : ℝ))^(k-2) ≤ c^k/2) :
    c^k/2 ≤ ‖∑ s ∈ primeProductSamples P k,
      kernelCoefficient P ε k s*(jacobiSym u s : ℂ)‖ := by
  apply kernelCoefficient_character_sum_lower_of_error_budget hP hJ ε hε hk heven u hc hmean
  have hy : ∀ p ∈ P, ε p*jacobiSym u p = -1 ∨ ε p*jacobiSym u p = 0 ∨ ε p*jacobiSym u p = 1 :=
    fun p hp => oriented_jacobi_trichotomy (ε p) u p (hε p hp)
  apply le_trans _ hbudget
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  exact add_le_add (abs_signAverage_le_one P hJ _ hy) le_rfl

end Ostmann.QuadraticCenter

end

end OAI
