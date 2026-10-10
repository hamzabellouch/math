import OAI.NumberTheory.Ostmann.Construction.ScheduledPhaseNorm
import OAI.NumberTheory.Ostmann.Construction.FullAtomFourierEnergy
import OAI.NumberTheory.Ostmann.Construction.InitialConstituentPoisson

namespace OAI

/-! # A direct finite-frequency energy bound for the actual final amplitude -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap FourierTransform

private theorem finite_sum_norm_sq_le {D : Type*} [Fintype D]
    (F : D → ℂ) (E : ℝ) (hE : 0 ≤ E) (hF : ∀ d, ‖F d‖ ^ 2 ≤ E) :
    ‖∑ d, F d‖ ^ 2 ≤ (Fintype.card D : ℝ) ^ 2 * E := by
  have hn : ‖∑ d, F d‖ ≤ (Fintype.card D : ℝ) * Real.sqrt E := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _d : D, Real.sqrt E :=
        Finset.sum_le_sum (fun d _ => Real.le_sqrt_of_sq_le (hF d))
      _ = _ := by simp
  calc
    _ ≤ ((Fintype.card D : ℝ) * Real.sqrt E) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hE]

noncomputable def constituentPrimeCoefficient {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) (q : SurvivingConstituent role size n → P) : ℂ :=
  ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf n
    (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod)
    (hist d) * (if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
      scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
        χ κ pivot n (hist d) P hP q center else 0)

theorem constituentPrimeCoefficient_energy {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (pivot : ℕ → (Σ i, Fin (size i))) (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hist : D → FrequencyTree ℤ n) (center : ∀ p : ℕ, ZMod p)
    (q : SurvivingConstituent role size n → P) :
    ‖constituentPrimeCoefficient role size χ κ pivot n P hP childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) hist center q‖ ^ 2 ≤
    (Fintype.card D : ℝ) ^ 2 *
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  apply finite_sum_norm_sq_le _ _ (Real.exp_pos _).le
  intro d
  have hw := fullAtomFourierWeight_square_exp_le role childBound pivotBound ranges ψ
    X lo hi Δ C K hX hlo hψ n
    (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod) (hist d)
  by_cases hq : Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ))
  · rw [ite_eq_left hq, norm_mul, mul_pow]
    have hp := scheduledSamplePhase_norm_le_one (fun i : Σ a, Fin (size a) => role i.1)
      χ κ hκ pivot n (hist d) P hP q center
    exact (mul_le_of_le_one_right (sq_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hp)).trans hw
  · rw [ite_eq_right hq, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact (Real.exp_pos _).le

theorem constituentPrimeGuardedAmplitude_eq_mean {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (center : ∀ p : ℕ, ZMod p) :
    constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
      childBound pivotBound ranges leaf hist center =
    ∑ q : SurvivingConstituent role size n → P,
      ((∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i) : ℝ) : ℂ) *
      constituentPrimeCoefficient role size χ κ pivot n P hP childBound pivotBound ranges
        leaf hist center q := rfl

theorem constituentPrimeCoefficient_mean_energy {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (pivot : ℕ → (Σ i, Fin (size i))) (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ i, Fin (size i)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hist : D → FrequencyTree ℤ n) (center : ∀ p : ℕ, ZMod p) :
    (∑ q : SurvivingConstituent role size n → P,
      (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) *
        ‖constituentPrimeCoefficient role size χ κ pivot n P hP childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) hist center q‖ ^ 2) ≤
      (Fintype.card D : ℝ) ^ 2 *
        Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  have hmass : (∑ q : SurvivingConstituent role size n → P,
      ∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) = 1 := by
    rw [← Fintype.prod_sum]
    have hi (i : SurvivingConstituent role size n) :
        (∑ p : P, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) p) = 1 :=
      primeSubsetPrior_mass P _ (hQP _) (hQ _)
    simp only [hi, Finset.prod_const_one]
  calc
    _ ≤ ∑ q : SurvivingConstituent role size n → P,
        (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) *
          ((Fintype.card D : ℝ) ^ 2 *
            Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K))) := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left
        (constituentPrimeCoefficient_energy role size χ κ hκ pivot n P hP childBound pivotBound
          ranges ψ X lo hi Δ C K hX hlo hψ hist center q)
        (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg _ _ _))
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

end Ostmann

end OAI
