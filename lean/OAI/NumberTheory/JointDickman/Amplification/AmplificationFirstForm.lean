import OAI.NumberTheory.JointDickman.Amplification.AmplificationReindex
import OAI.NumberTheory.JointDickman.Amplification.WeightedCauchy

namespace OAI

/-! # The first divisor form and its quadratic energy -/

namespace JointDickman
open Finset

noncomputable def firstFormWeight (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (D : Finset ℕ) (m : ℕ) : ℝ :=
  u (∏ p ∈ D, p) * regularCoefficientWeight B L τ C (∏ p ∈ D, p) *
    arithmeticResidueWeight B L τ C m

open Classical in
noncomputable def firstFormInner (B L : ℕ) (τ C : ℝ) (v : ℕ → ℕ → ℝ)
    (J : ℕ → ℂ) (N : ℕ) (D : Finset ℕ) (m : ℕ) : ℂ :=
  ∑ A ∈ (auxiliaryPrimes B).powerset,
    let a := ∏ p ∈ A, p
    let c := ∏ p ∈ D, p
    if a*m < N ∧ c ∣ a*m+1 then
      ((regularCoefficientWeight B L τ C a *
        arithmeticResidueWeight B L τ C ((a*m+1)/c) * v a c : ℝ) : ℂ) * J (a*m)
    else 0

noncomputable def firstDivisorForm (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (g J : ℕ → ℂ) (N : ℕ) : ℂ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    (firstFormWeight B L τ C u i.1 i.2 : ℂ) * star (g i.2) *
      firstFormInner B L τ C v J N i.1 i.2) / (N : ℂ)

noncomputable def firstFormVolume (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    firstFormWeight B L τ C u i.1 i.2) / (N : ℝ)

noncomputable def firstFormEnergy (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (J : ℕ → ℂ) (N : ℕ) : ℝ :=
  (∑ i ∈ (auxiliaryPrimes B).powerset ×ˢ range N,
    firstFormWeight B L τ C u i.1 i.2 * ‖firstFormInner B L τ C v J N i.1 i.2‖^2) / (N : ℝ)

theorem amplification_first_form (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (g J : ℕ → ℂ) (N : ℕ)
    (hg : ∀ A ∈ (auxiliaryPrimes B).powerset, ∀ m : ℕ, g ((∏ p ∈ A, p)*m) = g m) :
    amplificationDivisorForm B L τ C (fun a c => u c * v a c)
      (fun n => star (g n) * J n) N / (N : ℂ) = firstDivisorForm B L τ C u v g J N := by
  unfold amplificationDivisorForm firstDivisorForm
  congr 1
  rw [sum_product, sum_comm]
  apply sum_congr rfl
  intro D _
  rw [sum_comm]
  apply sum_congr rfl
  intro m _
  unfold firstFormInner
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  dsimp only
  by_cases h : (∏ p ∈ A, p)*m < N ∧ (∏ p ∈ D, p) ∣ (∏ p ∈ A, p)*m+1
  · rw [ite_eq_left h, ite_eq_left h, hg A hA m]
    unfold firstFormWeight
    push_cast
    ring
  · simp only [ite_eq_right h, mul_zero]

theorem firstFormWeight_nonneg (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (hu : ∀ c, 0 ≤ u c) (D : Finset ℕ) (m : ℕ) :
    0 ≤ firstFormWeight B L τ C u D m :=
  mul_nonneg (mul_nonneg (hu _) (regularCoefficientWeight_nonneg B L τ C _))
    (regularResidueWeight_nonneg B L τ C _)

/-- The Cauchy step removes the first label from the actual divisor form. -/
theorem firstDivisorForm_cauchy (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    (v : ℕ → ℕ → ℝ) (g J : ℕ → ℂ) (N : ℕ)
    (hu : ∀ c, 0 ≤ u c) (hg : ∀ m, ‖g m‖ ≤ 1) :
    ‖firstDivisorForm B L τ C u v g J N‖^2 ≤
      firstFormVolume B L τ C u N * firstFormEnergy B L τ C u v J N := by
  exact normalized_weighted_complex_cauchy (ι := Finset ℕ × ℕ)
    ((auxiliaryPrimes B).powerset ×ˢ range N)
    (fun i => firstFormWeight B L τ C u i.1 i.2) (fun i => star (g i.2))
    (fun i => firstFormInner B L τ C v J N i.1 i.2)
    (fun i _ => firstFormWeight_nonneg B L τ C u hu i.1 i.2)
    (fun i _ => by simpa only [norm_star] using hg i.2) (N := (N : ℝ)) (Nat.cast_nonneg N)

end JointDickman

end OAI
