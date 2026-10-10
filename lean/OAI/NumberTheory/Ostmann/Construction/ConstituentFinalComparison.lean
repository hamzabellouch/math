import OAI.NumberTheory.Ostmann.Construction.ConstituentRootCoefficient

namespace OAI

/-! # Applying final symmetrization to the actual guarded amplitude -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem constituent_final_comparison {I D R : Type*}
    [Fintype I] [Fintype D] [Fintype R]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (pivot : ℕ → (Σ i, Fin (size i))) (n m : ℕ)
    (word : Fin m ≃ {i : Σ a, Fin (size a) // role i.1 = .word})
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ i, Fin (size i)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (hist : D → FrequencyTree ℤ (n + 1)) (root : D → R)
    (center : ∀ p : ℕ, ZMod p) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ e f : FinalParityReassignments n m, e ≠ f → ∀ d d', root d = root d' →
      ‖∑ q : SurvivingConstituent role size (n + 1) → P,
        ((∏ i, primeSubsetPrior P (Q (copyScheduleOrigin (n + 1) i.val)) (q i) : ℝ) : ℂ) *
        (constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) center (hist d)
          (scheduledFullSamplePerm (fun i : Σ a, Fin (size a) => role i.1) n m word e q) *
        conj (constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound ranges
          (scheduleFourierLeaf role ψ X lo hi) center (hist d')
          (scheduledFullSamplePerm (fun i : Σ a, Fin (size a) => role i.1) n m word f q)))‖ ≤ E) :
    ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
      childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi) hist center‖ ^ 2 ≤
      (Fintype.card R : ℝ) *
        (((Fintype.card D : ℝ) ^ 2 *
          Real.exp (-(2 ^ (n + 1) : ℕ) * Δ + (2 ^ (n + 1) : ℕ) * (C + 2 * K))) /
            (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) + (Fintype.card D : ℝ) ^ 2 * E) := by
  let μ := fun i : Σ a, Fin (size a) => primeSubsetPrior P (Q i)
  let F := constituentPrimeRootCoefficient role size χ κ pivot (n + 1) P hP childBound
    pivotBound ranges (scheduleFourierLeaf role ψ X lo hi) center hist root
  have hm (i) : ∑ p : P, μ i p = 1 := primeSubsetPrior_mass P (Q i) (hQP i) (hQ i)
  have hc := scheduled_root_final_comparison (fun i : Σ a, Fin (size a) => role i.1)
    n m word μ (fun i p => primeSubsetPrior_nonneg P (Q i) p) hm F
    ((Fintype.card D : ℝ) ^ 2 *
      Real.exp (-(2 ^ (n + 1) : ℕ) * Δ + (2 ^ (n + 1) : ℕ) * (C + 2 * K)))
    ((Fintype.card D : ℝ) ^ 2 * E) (mul_nonneg (sq_nonneg _) hE)
    (constituentPrimeRootCoefficient_mean_energy role size χ κ pivot (n + 1) P hP
      childBound pivotBound ranges center Q hQP hQ hκ ψ X lo hi Δ C K hX hlo hψ hist root)
    (fun e f hef => ?_)
  · have he := constituentPrimeRootCoefficient_mean role size χ κ pivot (n + 1) P hP
      childBound pivotBound ranges (scheduleFourierLeaf role ψ X lo hi) center Q hist root
    change ‖∑ s, ∑ q, (scheduledPrimePrior (fun i : Σ a, Fin (size a) => role i.1)
      (n + 1) μ q : ℂ) * F s q‖ ^ 2 ≤ _ at hc
    change (∑ s, ∑ q, (scheduledPrimePrior (fun i : Σ a, Fin (size a) => role i.1)
      (n + 1) μ q : ℂ) * F s q) = _ at he
    rw [he] at hc
    exact hc
  · have hh := rootFibreSum_pair_bound root root
      (scheduledPrimePrior (fun i : Σ a, Fin (size a) => role i.1) (n + 1) μ)
      (fun d q => constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound
        ranges (scheduleFourierLeaf role ψ X lo hi) center (hist d)
        (scheduledFullSamplePerm (fun i : Σ a, Fin (size a) => role i.1) n m word e q))
      (fun d q => constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound
        ranges (scheduleFourierLeaf role ψ X lo hi) center (hist d)
        (scheduledFullSamplePerm (fun i : Σ a, Fin (size a) => role i.1) n m word f q))
      E hE (hpair e f hef)
    simpa only [F, constituentPrimeRootCoefficient, Complex.star_def, pow_two, mul_assoc] using hh

end Ostmann

end OAI
