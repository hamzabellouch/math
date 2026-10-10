import OAI.NumberTheory.Ostmann.Construction.ConstituentTransferWeight
import OAI.NumberTheory.Ostmann.Construction.FullWeightFrequencies
import OAI.NumberTheory.Ostmann.Construction.TransferCopiedSupport

namespace OAI

/-! # Frequency units for the actual supported arithmetic coefficient -/

namespace Ostmann

open scoped BigOperators Classical

theorem constituentTransferWeight_full_ne_zero {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    fullAtomTransferWeight role childBound pivotBound ranges leaf n
      (scheduledInsertedAtoms role n M
        (fun h => ∏ k, (a.1 (constituentH role size n h k) : ℕ))
        (fun y => ∏ k, (u (constituentY role size n y k) : ℕ))) (hist a.2) ≠ 0 := by
  unfold constituentTransferWeight at hw
  split_ifs at hw
  · exact (mul_ne_zero_iff.mp hw).2
  · exact False.elim (hw rfl)

theorem constituentTransferWeight_frequency_unit {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (hzero : ∀ x, fullAtomTransferWeight role childBound pivotBound ranges leaf 0 x (0 : ℤ) = 0)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0)
    (p : ℕ) [Fact p.Prime] (s : ℤ) (hs : s ∈ allFrequencyList n (hist a.2))
    (hsmall : s.natAbs < p) : (s : ZMod p) ≠ 0 := by
  have hf := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound ranges leaf hist u M a hw
  have hn := fullAtomTransferWeight_all_frequencies_ne_zero role childBound pivotBound ranges leaf
    hzero n _ (hist a.2) hf s hs
  exact isUnit_iff_ne_zero.mp (prime_large_frequency_unit s hn hsmall)

end Ostmann

end OAI
