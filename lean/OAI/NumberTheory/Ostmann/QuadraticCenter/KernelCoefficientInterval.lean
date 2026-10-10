import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientLower

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def kernelCoefficientInterval (S : ℕ) : Finset ℕ :=
  (Finset.Icc 1 S).filter (fun s => Squarefree s ∧ Odd s)

theorem primeProductSamples_subset_kernelCoefficientInterval {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    {H k : ℕ} (hH : ∀ p ∈ P, p ≤ H) :
    primeProductSamples P k ⊆ kernelCoefficientInterval (H^k) := by
  intro s hs
  have hh := primeProductSamples_properties hP ho hH hs
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Nat.pos_of_ne_zero hh.1.ne_zero, hh.2.2.1⟩, hh.1, hh.2.1⟩

theorem kernelCoefficient_interval_energy_le {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    (hJ : 0 < P.card) {H : ℕ} (hH : ∀ p ∈ P, p ≤ H)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1) (k : ℕ) :
    (∑ s ∈ kernelCoefficientInterval (H^k), ‖kernelCoefficient P ε k s‖^2) ≤
      (k.factorial : ℝ)/(P.card : ℝ)^k := by
  rw [kernelCoefficient_energy_eq_on_superset ε k
    (primeProductSamples_subset_kernelCoefficientInterval hP ho hH)]
  exact kernelCoefficient_energy_le hP hJ ε hε k

theorem kernelCoefficient_character_sum_eq_on_superset {P S : Finset ℕ}
    (ε : ℕ → ℤ) (k : ℕ) (u : ℤ) (hS : primeProductSamples P k ⊆ S) :
    (∑ s ∈ S, kernelCoefficient P ε k s*(jacobiSym u s : ℂ)) =
      ∑ s ∈ primeProductSamples P k, kernelCoefficient P ε k s*(jacobiSym u s : ℂ) := by
  symm
  apply Finset.sum_subset hS
  intro s hs hn
  rw [kernelCoefficient_eq_zero_of_not_mem P ε k s hn, zero_mul]

theorem kernelCoefficient_interval_character_sum {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    {H : ℕ} (hH : ∀ p ∈ P, p ≤ H) (ε : ℕ → ℤ) (k : ℕ) (u : ℤ) :
    (∑ s ∈ kernelCoefficientInterval (H^k), kernelCoefficient P ε k s*(jacobiSym u s : ℂ)) =
      (distinctSignAverage P (fun p => ε p*jacobiSym u p) k : ℂ) := by
  rw [kernelCoefficient_character_sum_eq_on_superset ε k u
    (primeProductSamples_subset_kernelCoefficientInterval hP ho hH), kernelCoefficient_character_sum hP]

theorem kernelCoefficient_interval_lower {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (ho : ∀ p ∈ P, Odd p)
    (hJ : 0 < P.card) {H : ℕ} (hH : ∀ p ∈ P, p ≤ H)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1)
    {k : ℕ} (hk : 2 ≤ k) (heven : Even k) {c : ℝ} (hc : 0 ≤ c)
    (hbudget : (((k : ℝ)+1)*(k : ℝ)^2/P.card) *
      (1+(k : ℝ)/Real.sqrt (P.card : ℝ))^(k-2) ≤ c^k/2)
    (u : ℤ) (hmean : c ≤ |signAverage P (fun p => ε p*jacobiSym u p)|) :
    c^k/2 ≤ ‖∑ s ∈ kernelCoefficientInterval (H^k),
      kernelCoefficient P ε k s*(jacobiSym u s : ℂ)‖ := by
  rw [kernelCoefficient_character_sum_eq_on_superset ε k u
    (primeProductSamples_subset_kernelCoefficientInterval hP ho hH)]
  exact kernelCoefficient_character_sum_lower hP hJ ε hε hk heven u hc hmean hbudget

end Ostmann.QuadraticCenter

end

end OAI
