import OAI.NumberTheory.Ostmann.Construction.ConstituentCopiedAssignment
import OAI.NumberTheory.Ostmann.Construction.ConstituentPivotEnumeration
import OAI.NumberTheory.Ostmann.Construction.InsertedAtomAssignment

namespace OAI

/-! # Grouping the current prime sample into its actual composite pivot -/

namespace Ostmann

open scoped BigOperators Classical

theorem copyConstituentEquiv_positive_inverse {I : Type*} (size : I → ℕ)
    (n : ℕ) (p : I) (k : Fin (size (copyScheduleOrigin n (copySchedulePositive n p)))) :
    (copyConstituentEquiv size n).symm ⟨copySchedulePositive n p, k⟩ =
      copySchedulePositive n ⟨p, ⟨k.val, by
        simpa only [copyScheduleOrigin_positive] using k.isLt⟩⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact congrArg (fun j => Sum.inl (true, j)) (ih k)

theorem constituent_pivot_entry {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (hu : ∀ i, role i = .pivot n → i = p)
    (k : Fin (size (copyScheduleOrigin n (copySchedulePositive n p)))) :
    (survivingConstituentEquiv role size n).symm
        ⟨scheduledPartitionEquiv role n (.inl ⟨p, hp⟩), k⟩ =
      enumeratedPartitionEquiv (fun i : Σ a, Fin (size a) => role i.1) n (size p)
        (pivotConstituentEquiv role size n p hp hu)
        (.inl ⟨k.val, by simpa only [copyScheduleOrigin_positive] using k.isLt⟩) := by
  apply Subtype.ext
  exact copyConstituentEquiv_positive_inverse size n p k

/-- The current prime assignment groups to the inserted atom state. In
particular the pivot value is the product of all its original constituents. -/
theorem constituent_partition_assignment {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (n : ℕ) (p : I) (hp : role p = .pivot n)
    (hu : ∀ i, role i = .pivot n → i = p)
    (u : CopyScheduleY (fun i : Σ a, Fin (size a) => role i.1) n → ℕ)
    (x : Fin (size p) → ℕ)
    (l : CopyScheduleH (fun i : Σ a, Fin (size a) => role i.1) n → ℕ) :
    (fun v => ((scheduleConstituentWord role size n v).map
        (scheduledPartitionAssignment (fun i : Σ a, Fin (size a) => role i.1)
          n (size p) (pivotConstituentEquiv role size n p hp hu) u x l)).prod) =
      scheduledInsertedAtoms role n (∏ k, x k)
        (fun h => ∏ k, l (constituentH role size n h k))
        (fun y => ∏ k, u (constituentY role size n y k)) := by
  funext v
  obtain ⟨j, rfl⟩ := (scheduledPartitionEquiv role n).surjective v
  rcases j with q | h | y
  · obtain ⟨a, ha⟩ := q
    have he : a = p := hu a ha
    subst a
    rw [scheduledInsertedAtoms_pivot, scheduleConstituentWord_prod]
    apply Fintype.prod_equiv (finCongr (congrArg size (copyScheduleOrigin_positive n p)))
    intro k
    rw [constituent_pivot_entry role size n p hp hu k]
    exact scheduledPartitionAssignment_apply _ _ _ _ _ _ _ (.inl _)
  · rw [scheduleConstituentWord_prod]
    change _ = scheduledInsertedAtoms role n (∏ k, x k)
      (fun h => ∏ k, l (constituentH role size n h k))
      (fun y => ∏ k, u (constituentY role size n y k)) ⟨h.val, h.property.1⟩
    rw [scheduledInsertedAtoms_H]
    apply Finset.prod_congr rfl
    intro k _
    exact scheduledPartitionAssignment_apply _ _ _ _ _ _ _ (.inr (.inl (constituentH role size n h k)))
  · rw [scheduleConstituentWord_prod]
    change _ = scheduledInsertedAtoms role n (∏ k, x k)
      (fun h => ∏ k, l (constituentH role size n h k))
      (fun y => ∏ k, u (constituentY role size n y k)) ⟨y.val, y.property.1⟩
    rw [scheduledInsertedAtoms_Y]
    apply Finset.prod_congr rfl
    intro k _
    exact scheduledPartitionAssignment_apply _ _ _ _ _ _ _ (.inr (.inr (constituentY role size n y k)))

end Ostmann

end OAI
