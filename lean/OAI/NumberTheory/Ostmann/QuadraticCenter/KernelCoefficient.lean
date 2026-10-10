import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientInterval

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem kernelCoefficient_package {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    (hJ : 0 < P.card) {H : ℕ} (hH : ∀ p ∈ P, p ≤ H)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) {c : ℝ} (hc : 0 ≤ c)
    (hbudget : (((k : ℝ)+1)*(k : ℝ)^2/P.card) *
      (1+(k : ℝ)/Real.sqrt (P.card : ℝ))^(k-2) ≤ c^k/2) :
    (∀ s, kernelCoefficient P ε k s ≠ 0 →
      0 < s ∧ Squarefree s ∧ Odd s ∧ s ≤ H^k ∧ s.primeFactors.card = k) ∧
    (∑ s ∈ kernelCoefficientInterval (H^k), ‖kernelCoefficient P ε k s‖^2) ≤
      (k.factorial : ℝ)/(P.card : ℝ)^k ∧
    (∀ u : ℤ, c ≤ |signAverage P (fun p => ε p*jacobiSym u p)| →
      c^k/2 ≤ ‖∑ s ∈ kernelCoefficientInterval (H^k),
        kernelCoefficient P ε k s*(jacobiSym u s : ℂ)‖) := by
  exact ⟨fun s hs => kernelCoefficient_support_properties hP ho hH ε hs,
    kernelCoefficient_interval_energy_le hP ho hJ hH ε hε k,
    fun u hu => kernelCoefficient_interval_lower hP ho hJ hH ε hε hk heven hc hbudget u hu⟩

end Ostmann.QuadraticCenter

end

end OAI
