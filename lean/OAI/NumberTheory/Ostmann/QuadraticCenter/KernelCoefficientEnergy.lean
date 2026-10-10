import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelCoefficientBasic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem kernelCoefficient_energy_eq {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1) (k : ℕ) :
    (∑ s ∈ primeProductSamples P k, ‖kernelCoefficient P ε k s‖^2) =
      (Nat.choose P.card k : ℝ)*((k.factorial : ℝ)/(P.card : ℝ)^k)^2 := by
  calc
    _ = ∑ _s ∈ primeProductSamples P k, ((k.factorial : ℝ)/(P.card : ℝ)^k)^2 :=
      Finset.sum_congr rfl (fun s hs => by rw [kernelCoefficient_norm hP ε hε hs])
    _ = _ := by simp only [Finset.sum_const, primeProductSamples_card hP, nsmul_eq_mul]

theorem kernelCoefficient_energy_le {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (hJ : 0 < P.card) (ε : ℕ → ℤ) (hε : ∀ p ∈ P, ε p = -1 ∨ ε p = 1) (k : ℕ) :
    (∑ s ∈ primeProductSamples P k, ‖kernelCoefficient P ε k s‖^2) ≤
      (k.factorial : ℝ)/(P.card : ℝ)^k := by
  rw [kernelCoefficient_energy_eq hP ε hε]
  let a : ℝ := (k.factorial : ℝ)/(P.card : ℝ)^k
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hJ0 : (0 : ℝ) < P.card := by exact_mod_cast hJ
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hchoose := (Nat.choose_le_pow_div k P.card : (Nat.choose P.card k : ℝ) ≤ (P.card : ℝ)^k/k.factorial)
  have hnorm : (Nat.choose P.card k : ℝ)*a ≤ 1 := by
    calc
      _ ≤ ((P.card : ℝ)^k/k.factorial)*a := mul_le_mul_of_nonneg_right hchoose ha
      _ = 1 := by dsimp [a]; field_simp
  change (Nat.choose P.card k : ℝ)*a^2 ≤ a
  calc
    _ = ((Nat.choose P.card k : ℝ)*a)*a := by ring
    _ ≤ 1*a := mul_le_mul_of_nonneg_right hnorm ha
    _ = _ := one_mul _

theorem kernelCoefficient_energy_eq_on_superset {P S : Finset ℕ} (ε : ℕ → ℤ) (k : ℕ)
    (hS : primeProductSamples P k ⊆ S) :
    (∑ s ∈ S, ‖kernelCoefficient P ε k s‖^2) =
      ∑ s ∈ primeProductSamples P k, ‖kernelCoefficient P ε k s‖^2 := by
  symm
  apply Finset.sum_subset hS
  intro s hs hn
  rw [kernelCoefficient_eq_zero_of_not_mem P ε k s hn, norm_zero, zero_pow (by decide)]

end Ostmann.QuadraticCenter

end

end OAI
