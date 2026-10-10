import OAI.NumberTheory.Ostmann.Arithmetic.AtomIntervalRanges
import OAI.NumberTheory.Ostmann.Construction.ConstituentPriorBounds

namespace OAI

/-! # Original atom intervals discharge the support clauses of the transfer -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_inserted_pivot_bounds {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (n : ℕ) (p : I) (hp : role p = .pivot n) (M : ℕ)
    (l : CopyScheduleH role n → ℕ) (u : CopyScheduleY role n → ℕ) (t : FrequencyTree ℤ n)
    (hw : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M l u) t ≠ 0) : lo p ≤ M ∧ M ≤ hi p := by
  let v := scheduledPartitionEquiv role n (.inl ⟨p, hp⟩)
  have hr : atomInterval role lo hi n v ∈ atomIntervalRanges role lo hi n :=
    List.mem_map.mpr ⟨v, Finset.mem_toList.mpr (Finset.mem_univ v), rfl⟩
  have hh := (atomInterval_holds_iff role lo hi n v _).mp
    (fullAtomTransferWeight_top_range role childBound pivotBound _ leaf n _ t hw _ hr)
  dsimp only [v] at hh
  rw [scheduledInsertedAtoms_pivot] at hh
  simpa only [scheduledPartitionEquiv_pivot, copyScheduleOrigin_positive] using hh

theorem constituentTransferWeight_copied_intervals {I D : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (size : I → ℕ) (lo hi : I → ℕ) (n : ℕ)
    (P : Finset ℕ) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (hist : D → FrequencyTree ℤ n)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → P) (M : ℕ)
    (a b : (CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → P) × D)
    (ha : constituentTransferWeight role size n P Q childBound pivotBound
      (atomIntervalRanges role lo hi) leaf hist u M a ≠ 0)
    (hb : constituentTransferWeight role size n P Q childBound pivotBound
      (atomIntervalRanges role lo hi) leaf hist u M b ≠ 0) :
    ∀ c ∈ atomIntervalRanges role lo hi (n + 1),
      c.Holds (copiedConstituentAtomValues role size n P u a.1 b.1) := by
  have hL := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound
    (atomIntervalRanges role lo hi) leaf hist u M a ha
  have hR := constituentTransferWeight_full_ne_zero role size n P Q childBound pivotBound
    (atomIntervalRanges role lo hi) leaf hist u M b hb
  exact fullAtomTransferWeight_copied_intervals role lo hi childBound pivotBound leaf n M _ _ _
    (hist a.2) (hist b.2) hL hR

end Ostmann

end OAI
