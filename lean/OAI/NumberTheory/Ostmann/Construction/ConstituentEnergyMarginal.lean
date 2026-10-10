import OAI.NumberTheory.Ostmann.Construction.ConstituentFamilyEnergy
import OAI.NumberTheory.Ostmann.Construction.FixedPivotPrior

namespace OAI

/-! # The matching energy is the fixed-pivot marginal of the original prime law -/

namespace Ostmann
open scoped Classical BigOperators

theorem constituentHistoryEnergy_eq_fixedPivot {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n M : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hsub : ∀ i, Q i ⊆ P) (hmass : ∀ i, (∑ p ∈ Q i, (p : ℝ)⁻¹) ≠ 0)
    (p : I) (hp : role p = .pivot n) (hu : ∀ i, role i = .pivot n → i = p)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n) :
    constituentHistoryEnergy role size n P Q childBound pivotBound ranges leaf hist M =
      ∑ d : D, ∑ q : SurvivingConstituent role size n → P,
        scheduledPrimePrior (fun i : Σ a, Fin (size a) => role i.1) n
          (fun i => primeSubsetPrior P (Q i)) q *
        ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
          (scheduledReplacePivot role n M
            (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))
          (hist d)‖ ^ 2 := by
  have hf := constituent_fixedPivot_prior_fubini role size n M p hp hu P
    (fun i => primeSubsetPrior P (Q (copyScheduleOrigin n i.val)))
    (fun i => primeSubsetPrior_mass P _ (hsub _) (hmass _))
    (fun d x => ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n x (hist d)‖ ^ 2)
  dsimp only at hf
  simp only [enumeratedPartitionEquiv_rest, Sum.elim_inl, Sum.elim_inr] at hf
  change _ = ∑ d : D, ∑ q : SurvivingConstituent role size n → P,
    (∏ i, primeSubsetPrior P (Q (copyScheduleOrigin n i.val)) (q i)) *
      ‖fullAtomTransferWeight role childBound pivotBound ranges leaf n
        (scheduledReplacePivot role n M
          (fun a => ((scheduleConstituentWord role size n a).map (fun v => (q v : ℕ))).prod))
        (hist d)‖ ^ 2
  rw [hf]
  unfold constituentHistoryEnergy
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

end Ostmann

end OAI
