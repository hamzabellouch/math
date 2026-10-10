import OAI.NumberTheory.Ostmann.Arithmetic.FiniteRootFibres
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalComparison

namespace OAI

/-! # Root-frequency fibres of the actual guarded prime coefficient -/

namespace Ostmann
open scoped BigOperators Classical SchwartzMap FourierTransform

section
variable {I D R : Type*} [Fintype I] [Fintype D] [Fintype R]
variable (role : I → CopyScheduleRole) (size : I → ℕ)
variable (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
variable (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
variable (n : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
variable (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
variable (leaf : ScheduleAtomState role → ℤ → ℂ)
variable (center : ∀ p : ℕ, ZMod p)

noncomputable def constituentPrimeTerm (t : FrequencyTree ℤ n)
    (q : SurvivingConstituent role size n → P) : ℂ :=
  fullAtomTransferWeight role childBound pivotBound ranges leaf n
    (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod) t *
    (if Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ)) then
      scheduledSamplePhase (fun i : Σ a, Fin (size a) => role i.1)
        χ κ pivot n t P hP q center else 0)

noncomputable def constituentPrimeRootCoefficient (hist : D → FrequencyTree ℤ n)
    (root : D → R) (s : R) (q : SurvivingConstituent role size n → P) : ℂ :=
  rootFibreSum root s (fun d => constituentPrimeTerm role size χ κ pivot n P hP
    childBound pivotBound ranges leaf center (hist d) q)

theorem constituentPrimeRootCoefficient_sum (hist : D → FrequencyTree ℤ n)
    (root : D → R) (q : SurvivingConstituent role size n → P) :
    (∑ s, constituentPrimeRootCoefficient role size χ κ pivot n P hP childBound pivotBound
      ranges leaf center hist root s q) =
    constituentPrimeCoefficient role size χ κ pivot n P hP childBound pivotBound ranges leaf hist center q := by
  exact sum_rootFibreSum root _

omit [Fintype D] [Fintype R] in
theorem constituentPrimeTerm_energy
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ)
    (hX : 0 < X) (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (t : FrequencyTree ℤ n) (q : SurvivingConstituent role size n → P) :
    ‖constituentPrimeTerm role size χ κ pivot n P hP childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo hi) center t q‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  have hw := fullAtomFourierWeight_square_exp_le role childBound pivotBound ranges ψ
    X lo hi Δ C K hX hlo hψ n
    (fun v => ((scheduleConstituentWord role size n v).map (fun i => (q i : ℕ))).prod) t
  unfold constituentPrimeTerm
  by_cases hq : Pairwise (fun i j => (q i : ℕ).Coprime (q j : ℕ))
  · rw [ite_eq_left hq, norm_mul, mul_pow]
    have hp := scheduledSamplePhase_norm_le_one (fun i : Σ a, Fin (size a) => role i.1)
      χ κ hκ pivot n t P hP q center
    exact (mul_le_of_le_one_right (sq_nonneg _)
      (pow_le_one₀ (norm_nonneg _) hp)).trans hw
  · rw [ite_eq_right hq, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact (Real.exp_pos _).le

theorem constituentPrimeRootCoefficient_energy
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ)
    (hX : 0 < X) (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hist : D → FrequencyTree ℤ n) (root : D → R)
    (q : SurvivingConstituent role size n → P) :
    (∑ s, ‖constituentPrimeRootCoefficient role size χ κ pivot n P hP childBound pivotBound
      ranges (scheduleFourierLeaf role ψ X lo hi) center hist root s q‖ ^ 2) ≤
      (Fintype.card D : ℝ) ^ 2 * Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  apply rootFibreSum_energy _ _ _ (Real.exp_pos _).le
  intro d
  exact constituentPrimeTerm_energy role size χ κ pivot n P hP childBound pivotBound ranges
    center hκ ψ X lo hi Δ C K hX hlo hψ (hist d) q

theorem constituentPrimeRootCoefficient_mean
    (Q : (Σ i, Fin (size i)) → Finset ℕ) (hist : D → FrequencyTree ℤ n) (root : D → R) :
    (∑ s, ∑ q : SurvivingConstituent role size n → P,
      ((∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i) : ℝ) : ℂ) *
        constituentPrimeRootCoefficient role size χ κ pivot n P hP childBound pivotBound
          ranges leaf center hist root s q) =
      constituentPrimeGuardedAmplitude role size χ κ pivot n P hP Q
        childBound pivotBound ranges leaf hist center := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, constituentPrimeRootCoefficient_sum]
  rfl

theorem constituentPrimeRootCoefficient_mean_energy
    (Q : (Σ i, Fin (size i)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (hκ : ∀ i p, ‖κ i p‖ ≤ 1) (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ)
    (hX : 0 < X) (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hist : D → FrequencyTree ℤ n) (root : D → R) :
    (∑ s, ∑ q : SurvivingConstituent role size n → P,
      (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) *
        ‖constituentPrimeRootCoefficient role size χ κ pivot n P hP childBound pivotBound
          ranges (scheduleFourierLeaf role ψ X lo hi) center hist root s q‖ ^ 2) ≤
      (Fintype.card D : ℝ) ^ 2 * Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  have hmass : (∑ q : SurvivingConstituent role size n → P,
      ∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) = 1 := by
    rw [← Fintype.prod_sum]
    have hi (i : SurvivingConstituent role size n) :
        (∑ p : P, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) p) = 1 :=
      primeSubsetPrior_mass P _ (hQP _) (hQ _)
    simp only [hi, Finset.prod_const_one]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ q : SurvivingConstituent role size n → P,
        (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) *
          ((Fintype.card D : ℝ) ^ 2 *
            Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K))) := by
      apply Finset.sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left
        (constituentPrimeRootCoefficient_energy role size χ κ pivot n P hP childBound pivotBound
          ranges center hκ ψ X lo hi Δ C K hX hlo hψ hist root q)
        (Finset.prod_nonneg (fun i _ => primeSubsetPrior_nonneg _ _ _))
    _ = _ := by rw [← Finset.sum_mul, hmass, one_mul]

end
end Ostmann

end OAI
