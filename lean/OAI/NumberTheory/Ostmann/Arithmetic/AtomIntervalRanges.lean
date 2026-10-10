import OAI.NumberTheory.Ostmann.Construction.FullAtomRangeSupport
import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedSupport

namespace OAI

/-! # Concrete inherited intervals for every original atom role -/

namespace Ostmann

open scoped Classical

noncomputable def atomInterval {I : Type*} (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) : ScheduleAtomRange role n where
  atoms := [v]
  lower := lo (copyScheduleOrigin n v.val)
  upper := hi (copyScheduleOrigin n v.val)

noncomputable def atomIntervalRanges {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) : List (ScheduleAtomRange role n) :=
  Finset.univ.toList.map (atomInterval role lo hi n)

theorem atomInterval_holds_iff {I : Type*} (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) (v : CopyScheduleAtoms role n) (x : CopyScheduleAtoms role n → ℕ) :
    (atomInterval role lo hi n v).Holds x ↔
      lo (copyScheduleOrigin n v.val) ≤ x v ∧ x v ≤ hi (copyScheduleOrigin n v.val) := by
  simp only [atomInterval, ScheduleAtomRange.Holds, List.map_singleton, List.prod_singleton,
    Set.mem_Icc, Nat.cast_le]

theorem atomIntervalRanges_holds_iff {I : Type*} [Fintype I] (role : I → CopyScheduleRole)
    (lo hi : I → ℕ) (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) :
    (∀ r ∈ atomIntervalRanges role lo hi n, r.Holds x) ↔
      ∀ v, lo (copyScheduleOrigin n v.val) ≤ x v ∧ x v ≤ hi (copyScheduleOrigin n v.val) := by
  constructor
  · intro h v
    apply (atomInterval_holds_iff role lo hi n v x).mp
    apply h
    exact List.mem_map.mpr ⟨v, Finset.mem_toList.mpr (Finset.mem_univ v), rfl⟩
  · intro h r hr
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hr
    exact (atomInterval_holds_iff role lo hi n v x).mpr (h v)

/-- Copying preserves the original atom origin and hence its exact interval. -/
theorem atomIntervalRanges_copied {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ) (n M : ℕ)
    (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ)
    (hL : ∀ a ∈ atomIntervalRanges role lo hi n,
      a.Holds (scheduledInsertedAtoms role n M l u))
    (hR : ∀ a ∈ atomIntervalRanges role lo hi n,
      a.Holds (scheduledInsertedAtoms role n M r u)) :
    ∀ a ∈ atomIntervalRanges role lo hi (n + 1),
      a.Holds (scheduledCopiedAssignment role n u l r) := by
  apply (atomIntervalRanges_holds_iff role lo hi (n + 1) _).mpr
  have hL' := (atomIntervalRanges_holds_iff role lo hi n _).mp hL
  have hR' := (atomIntervalRanges_holds_iff role lo hi n _).mp hR
  intro v
  obtain ⟨j, rfl⟩ := (copyScheduleSurvivorEquiv role n).symm.surjective v
  rcases j with ⟨b, h⟩ | y
  · cases b
    · have hh := hR' ⟨h.val, h.property.1⟩
      change lo (copyScheduleOrigin n h.val) ≤ r h ∧ r h ≤ hi (copyScheduleOrigin n h.val)
      simpa only [scheduledInsertedAtoms_H] using hh
    · have hh := hL' ⟨h.val, h.property.1⟩
      change lo (copyScheduleOrigin n h.val) ≤ l h ∧ l h ≤ hi (copyScheduleOrigin n h.val)
      simpa only [scheduledInsertedAtoms_H] using hh
  · have hh := hL' ⟨y.val, y.property.1⟩
    change lo (copyScheduleOrigin n y.val) ≤ u y ∧ u y ≤ hi (copyScheduleOrigin n y.val)
    simpa only [scheduledInsertedAtoms_Y] using hh

/-- Both old full coefficients enforce every new interval. This discharges
the interval clause in the actual guarded arithmetic step. -/
theorem fullAtomTransferWeight_copied_intervals {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (lo hi : I → ℕ)
    (childBound pivotBound : ℕ → ℕ) (leaf : ScheduleAtomState role → ℤ → ℂ)
    (n M : ℕ) (u : CopyScheduleY role n → ℕ) (l r : CopyScheduleH role n → ℕ)
    (t t' : FrequencyTree ℤ n)
    (hL : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M l u) t ≠ 0)
    (hR : fullAtomTransferWeight role childBound pivotBound (atomIntervalRanges role lo hi) leaf n
      (scheduledInsertedAtoms role n M r u) t' ≠ 0) :
    ∀ a ∈ atomIntervalRanges role lo hi (n + 1), a.Holds (scheduledCopiedAssignment role n u l r) := by
  exact atomIntervalRanges_copied role lo hi n M u l r
    (fun a ha => fullAtomTransferWeight_top_range role childBound pivotBound _ leaf n _ t hL a ha)
    (fun a ha => fullAtomTransferWeight_top_range role childBound pivotBound _ leaf n _ t' hR a ha)

end Ostmann

end OAI
