import OAI.NumberTheory.Ostmann.Construction.InsertedAtomSupport
import OAI.NumberTheory.Ostmann.Construction.PrimeTupleSupport

namespace OAI

/-! # The original constituent support in the arithmetic coefficient -/

namespace Ostmann

open scoped BigOperators Classical

/-- Pairwise prime support is retained inside each grouped atom as well as
between atoms. The reconstructed pivot remains a single integer parameter. -/
noncomputable def constituentTransferWeight {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D) : ℂ :=
  if Pairwise (fun i j =>
      (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) j)) then
    constituentCurrentWeight role size n P Q childBound pivotBound ranges leaf hist u M a
  else 0

/-- Both coprimality clauses of the arithmetic transfer are now consequences
of the concrete coefficient's support. -/
theorem constituentTransferWeight_support {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (hw : constituentTransferWeight role size n P Q childBound pivotBound ranges leaf hist u M a ≠ 0) :
    Pairwise (fun i j =>
      (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) i).Coprime
        (Sum.elim (fun h => (a.1 h : ℕ)) (fun y => (u y : ℕ)) j)) ∧
      M.Coprime ((∏ h, (a.1 h : ℕ)) * ∏ y, (u y : ℕ)) ∧
      M.Coprime (frequencyRoot n (hist a.2)).natAbs := by
  unfold constituentTransferWeight at hw
  split_ifs at hw with hg
  · exact ⟨hg,
      constituentCurrentWeight_pivot_coprime role size n p hp P Q childBound pivotBound ranges leaf hist u M a hw,
      constituentCurrentWeight_pivot_frequency_unit role size n p hp P Q childBound pivotBound ranges leaf hist u M a hw⟩
  · exact False.elim (hw rfl)

end Ostmann

end OAI
