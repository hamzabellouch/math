import OAI.NumberTheory.Ostmann.Characters.PublishedBonami

namespace OAI

/-! # The finite-cube inequality for a concrete family of distinct monomials -/

namespace Ostmann

open scoped BigOperators

private noncomputable def monomialCoefficients {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (a : ι → ℝ) (Q : Finset P) : ℝ :=
  ∑ i, if σ i = Q then a i else 0

private theorem monomialCoefficients_apply {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (hσ : Function.Injective σ)
    (a : ι → ℝ) (i : ι) : monomialCoefficients σ a (σ i) = a i := by
  classical
  unfold monomialCoefficients
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp only [ite_eq_right_iff]
    exact fun h => (hji (hσ h)).elim
  · simp

private theorem monomialCoefficients_sum {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (a : ι → ℝ) (F : Finset P → ℝ) :
    (∑ Q : Finset P, monomialCoefficients σ a Q * F Q) = ∑ i, a i * F (σ i) := by
  classical
  simp only [monomialCoefficients, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

private theorem monomialCoefficients_energy {ι : Type*} [Fintype ι]
    {P : Finset ℕ} (σ : ι → Finset P) (hσ : Function.Injective σ)
    (a : ι → ℝ) (F : Finset P → ℝ) :
    (∑ Q : Finset P, F Q * (monomialCoefficients σ a Q) ^ 2) =
      ∑ i, F (σ i) * (a i) ^ 2 := by
  classical
  have he (Q : Finset P) : (monomialCoefficients σ a Q) ^ 2 =
      monomialCoefficients σ (fun i => (a i) ^ 2) Q := by
    by_cases hQ : ∃ i, σ i = Q
    · obtain ⟨i, rfl⟩ := hQ
      rw [monomialCoefficients_apply σ hσ, monomialCoefficients_apply σ hσ]
    · have hne (i : ι) : σ i ≠ Q := fun hi => hQ ⟨i, hi⟩
      simp [monomialCoefficients, hne]
  simp_rw [he, mul_comm (F _)]
  rw [monomialCoefficients_sum]

/-- Apply the published cube bound after inserting the coefficient array
by zero outside the actual monomial family. -/
theorem bonami_monomial_family (hB : PublishedBonamiBound)
    {ι : Type*} [Fintype ι] (P : Finset ℕ)
    (σ : ι → Finset P) (hσ : Function.Injective σ) (a : ι → ℝ)
    (l : ℕ) (hl : 0 < l) :
    (Fintype.card (P → Bool) : ℝ)⁻¹ *
      ∑ ε : P → Bool, |∑ i, a i * rademacherMonomial (σ i) ε| ^ (2 * l) ≤
      (∑ i, ((2 * l - 1 : ℕ) : ℝ) ^ (σ i).card * (a i) ^ 2) ^ l := by
  have hb := hB P l hl (monomialCoefficients σ a)
  simp_rw [monomialCoefficients_sum] at hb
  rw [monomialCoefficients_energy σ hσ] at hb
  exact hb

end Ostmann

end OAI
