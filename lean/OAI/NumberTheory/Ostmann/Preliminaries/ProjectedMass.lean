import OAI.NumberTheory.Ostmann.Preliminaries.FiniteMass

namespace OAI

namespace Ostmann.Preliminaries
open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

noncomputable def projectedMass (π : α → β) (μ : α → ℝ) (r : β) : ℝ :=
  ∑ a, if π a = r then μ a else 0

omit [Fintype β] in
theorem projectedMass_nonneg (π : α → β) (μ : α → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (r : β) : 0 ≤ projectedMass π μ r := by
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp [hμ])

theorem projectedMass_sum (π : α → β) (μ : α → ℝ) :
    ∑ r, projectedMass π μ r = ∑ a, μ a := by
  simp only [projectedMass]
  rw [Finset.sum_comm]
  simp

omit [Fintype β] in
theorem projectedMass_eq_zero (π : α → β) (μ : α → ℝ) (S : Finset β)
    (hsupport : ∀ a, μ a ≠ 0 → π a ∈ S) {r : β} (hr : r ∉ S) :
    projectedMass π μ r = 0 := by
  apply Finset.sum_eq_zero
  intro a _
  by_cases heq : π a = r
  · simp only [heq, ite_true]
    by_contra hne
    exact hr (heq ▸ hsupport a hne)
  · simp [heq]

theorem projectedMass_test (π : α → β) (μ : α → ℝ) (f : β → ℝ) :
    ∑ r, projectedMass π μ r * f r = ∑ a, μ a * f (π a) := by
  simp only [projectedMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

theorem projectedMass_complex_test (π : α → β) (μ : α → ℝ) (f : β → ℂ) :
    ∑ r, (projectedMass π μ r : ℂ) * f r = ∑ a, (μ a : ℂ) * f (π a) := by
  simp only [projectedMass, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [apply_ite, Complex.ofReal_zero, ite_mul, zero_mul]
  simp

theorem projectedMass_energy (π : α → β) (μ : α → ℝ) :
    massEnergy (projectedMass π μ) =
      ∑ a, ∑ b, if π a = π b then μ a * μ b else 0 := by
  simp only [massEnergy, pow_two]
  rw [projectedMass_test]
  simp only [projectedMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases heq : π a = π b
  · simp [heq]
  · simp [heq, Ne.symm heq]

theorem massEnergy_le_cap (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (hmass : ∑ a, μ a = 1) {M : ℝ} (hcap : ∀ a, μ a ≤ M) :
    massEnergy μ ≤ M := by
  calc
    massEnergy μ = ∑ a, μ a * μ a := by simp only [massEnergy, pow_two]
    _ ≤ ∑ a, M * μ a := Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right (hcap a) (hμ a))
    _ = M := by rw [← Finset.mul_sum, hmass, mul_one]

end Ostmann.Preliminaries

end OAI
