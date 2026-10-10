import OAI.NumberTheory.Ostmann.Construction.ConstituentFinalSymmetrization
import OAI.NumberTheory.Ostmann.Construction.ConstituentScheduledEnergy
import OAI.NumberTheory.Ostmann.Construction.ScheduledHistoryError

namespace OAI

/-! # The final comparison for the genuine varying-cutoff history family -/

namespace Ostmann
open scoped BigOperators Classical ComplexConjugate

theorem scheduled_constituent_final_bound {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (hκ : ∀ i p, ‖κ i p‖ ≤ 1)
    (pivot : ℕ → (Σ i, Fin (size i))) (n m : ℕ)
    (word : Fin m ≃ {i : Σ a, Fin (size a) // role i.1 = .word})
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (Q : (Σ i, Fin (size i)) → Finset ℕ) (hQP : ∀ i, Q i ⊆ P)
    (hQ : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (V : ℕ → ℕ)
    (center : ∀ p : ℕ, ZMod p) (B E : ℝ) (hE : 0 ≤ E)
    (henergy : (∑ d : ScheduledFrequencyIndex V (n + 1),
      ∑ q : SurvivingConstituent role size (n + 1) → P,
        scheduledPrimePrior (fun j : Σ a, Fin (size a) => role j.1) (n + 1)
          (fun j => primeSubsetPrior P (Q j)) q *
        ‖fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1)
          (fun a => ((scheduleConstituentWord role size (n + 1) a).map (fun v => (q v : ℕ))).prod)
          (scheduledFrequencyHistory V (n + 1) d)‖ ^ 2) ≤ B)
    (hpair : ∀ e f : FinalParityReassignments n m, e ≠ f →
      ∀ d d' : ScheduledFrequencyIndex V (n + 1), d.1 = d'.1 →
      ‖∑ q : SurvivingConstituent role size (n + 1) → P,
        ((∏ i, primeSubsetPrior P (Q (copyScheduleOrigin (n + 1) i.val)) (q i) : ℝ) : ℂ) *
        (constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound ranges
          leaf center (scheduledFrequencyHistory V (n + 1) d) q *
        conj (constituentPrimeTerm role size χ κ pivot (n + 1) P hP childBound pivotBound ranges
          leaf center (scheduledFrequencyHistory V (n + 1) d')
          (fun i => q (scheduledFinalRelativePerm
            (fun i : Σ a, Fin (size a) => role i.1) n m word e f i))))‖ ≤ E) :
    ‖constituentPrimeGuardedAmplitude role size χ κ pivot (n + 1) P hP Q
      childBound pivotBound ranges leaf (scheduledFrequencyHistory V (n + 1)) center‖ ^ 2 ≤
      ((transferFrequencyRange (V (n + 1))).card : ℝ) *
        (B / (((Nat.factorial (2 ^ n)) ^ 2) ^ m : ℕ) +
          (Fintype.card (ScheduledFrequencyIndex V (n + 1)) : ℝ) ^ 2 * E) := by
  have hc := constituent_final_unique_comparison role size χ κ hκ pivot n m word P hP Q hQP hQ
    childBound pivotBound ranges leaf (scheduledFrequencyHistory V (n + 1))
    (scheduledFrequencyHistory_injective V (n + 1)) (fun d => d.1)
    (fun _ _ h => congrArg Subtype.val h) center E hE hpair
  simp only [Fintype.card_coe] at hc
  apply hc.trans
  change _ ≤ ((transferFrequencyRange (V (n + 1))).card : ℝ) * _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact add_le_add (div_le_div_of_nonneg_right henergy (Nat.cast_nonneg _)) le_rfl

end Ostmann

end OAI
