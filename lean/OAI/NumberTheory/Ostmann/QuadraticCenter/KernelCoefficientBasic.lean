import OAI.NumberTheory.Ostmann.QuadraticCenter.CompositeCenter
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductReindex
import OAI.NumberTheory.Ostmann.QuadraticCenter.RepeatAverage

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def kernelCoefficient (P : Finset ℕ) (ε : ℕ → ℤ) (k s : ℕ) : ℂ :=
  if s ∈ primeProductSamples P k then
    ((((k.factorial : ℝ)/(P.card : ℝ)^k) : ℝ) : ℂ) * ∏ p ∈ s.primeFactors, (ε p : ℂ)
  else 0

@[simp] theorem kernelCoefficient_eq_zero_of_not_mem (P : Finset ℕ) (ε : ℕ → ℤ)
    (k s : ℕ) (hs : s ∉ primeProductSamples P k) : kernelCoefficient P ε k s = 0 := by
  simp only [kernelCoefficient, ite_eq_right hs]

theorem kernelCoefficient_primeFactors_subset {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) {k s : ℕ} (hs : s ∈ primeProductSamples P k) :
    s.primeFactors ⊆ P := by
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hs
  exact primeSubsetProduct_primeFactors_subset hP U

theorem kernelCoefficient_norm {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1)
    {k s : ℕ} (hs : s ∈ primeProductSamples P k) :
    ‖kernelCoefficient P ε k s‖ = (k.factorial : ℝ)/(P.card : ℝ)^k := by
  rw [kernelCoefficient, ite_eq_left hs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), norm_prod]
  have hp : (∏ p ∈ s.primeFactors, ‖(ε p : ℂ)‖) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rcases hε p (kernelCoefficient_primeFactors_subset hP hs hp) with h | h <;> simp [h]
  rw [hp, mul_one]

theorem kernelCoefficient_support_properties {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    {H : ℕ} (hH : ∀ p ∈ P, p ≤ H) (ε : ℕ → ℤ) {k s : ℕ}
    (hs : kernelCoefficient P ε k s ≠ 0) :
    0 < s ∧ Squarefree s ∧ Odd s ∧ s ≤ H^k ∧ s.primeFactors.card = k := by
  have hm : s ∈ primeProductSamples P k := by
    by_contra hn
    exact hs (kernelCoefficient_eq_zero_of_not_mem P ε k s hn)
  have hp := primeProductSamples_properties hP ho hH hm
  exact ⟨Nat.pos_of_ne_zero hp.1.ne_zero, hp⟩

end Ostmann.QuadraticCenter

end

end OAI
