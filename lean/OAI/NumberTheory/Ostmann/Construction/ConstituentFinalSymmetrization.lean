import OAI.NumberTheory.Ostmann.Construction.ConstituentUniqueRootEnergy
import OAI.NumberTheory.Ostmann.Construction.ScheduledFinalPairReindex

namespace OAI

/-! # The actual final comparison with unique-history energy and relative pairs -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem constituent_final_unique_comparison {I D R : Type*}
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
    (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hist : D → FrequencyTree ℤ (n + 1)) (hhist : Function.Injective hist)
    (root : D → R)
    (hroot : ∀ d d', root d = root d' →
      frequencyRoot (n + 1) (hist d) = frequencyRoot (n + 1) (hist d'))
    (center : ∀ p : ℕ, ZMod p) (E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ e f : FinalParityReassignments n m, e ≠ f → ∀ d d', root d = root d' →
      ‖∑ q : SurvivingConstituent role size (n + 1) → P,
        ((∏ i, primeSubsetPrior P (Q (copyScheduleOrigin (n + 1) i.val)) (q i) : ℝ) : ℂ) *
        (constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound ranges
          leaf center (hist d) q *
        conj (constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound ranges
          leaf center (hist d') (fun i => q (scheduledFinalRelativePerm
            (fun i : Σ a, Fin (size a) => role i.1) n m word e f i))))‖ ≤ E) :
    ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
      childBound pivotBound ranges leaf hist center‖ ^ 2 ≤
      (Fintype.card R : ℝ) *
        ((∑ d, ∑ q : SurvivingConstituent role size (n + 1) → P,
          (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin (n + 1) i.val)) (q i)) *
          ‖fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
            (fun v => ((scheduleConstituentWord role size (n + 1) v).map
              (fun i => (q i : ℕ))).prod) (hist d)‖ ^ 2) /
            (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) + (Fintype.card D : ℝ) ^ 2 * E) := by
  let ρ := fun i : Σ a, Fin (size a) => role i.1
  let μ := fun i : Σ a, Fin (size a) => primeSubsetPrior P (Q i)
  let F := constituentPrimeRootCoefficient role size χ κ pivot (n + 1) P hP childBound
    pivotBound ranges leaf center hist root
  have hm (i) : ∑ p : P, μ i p = 1 := primeSubsetPrior_mass P (Q i) (hQP i) (hQ i)
  have hp (e f : FinalParityReassignments n m) (hef : e ≠ f) (d d')
      (hr : root d = root d') :
      ‖∑ q, (scheduledPrimePrior ρ (n + 1) μ q : ℂ) *
        (constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound ranges
          leaf center (hist d) (scheduledFullSamplePerm ρ n m word e q) *
        conj (constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound ranges
          leaf center (hist d') (scheduledFullSamplePerm ρ n m word f q)))‖ ≤ E := by
    rw [scheduled_final_pair_reindex]
    exact hpair e f hef d d' hr
  have hc := scheduled_root_final_comparison ρ n m word μ
    (fun i p => primeSubsetPrior_nonneg P (Q i) p) hm F _
    ((Fintype.card D : ℝ) ^ 2 * E) (mul_nonneg (sq_nonneg _) hE)
    (constituentPrimeRootCoefficient_mean_energy_unique role size χ κ pivot (n + 1) P hP
      childBound pivotBound ranges leaf center Q hκ hist hhist root hroot)
    (fun e f hef => ?_)
  · have he := constituentPrimeRootCoefficient_mean role size χ κ pivot (n + 1) P hP
      childBound pivotBound ranges leaf center Q hist root
    change ‖∑ s, ∑ q, (scheduledPrimePrior ρ (n + 1) μ q : ℂ) * F s q‖ ^ 2 ≤ _ at hc
    change (∑ s, ∑ q, (scheduledPrimePrior ρ (n + 1) μ q : ℂ) * F s q) = _ at he
    rw [he] at hc
    exact hc
  · have hh := rootFibreSum_pair_bound root root (scheduledPrimePrior ρ (n + 1) μ)
      (fun d q => constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound
        ranges leaf center (hist d) (scheduledFullSamplePerm ρ n m word e q))
      (fun d q => constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound
        ranges leaf center (hist d) (scheduledFullSamplePerm ρ n m word f q))
      E hE (hp e f hef)
    simpa only [F, constituentPrimeRootCoefficient, Complex.star_def, pow_two, mul_assoc] using hh

end Ostmann

end OAI
