import OAI.NumberTheory.Ostmann.Construction.ReverseAtomSources
import OAI.NumberTheory.Ostmann.Construction.ExpandedScheduleCoordinates

namespace OAI

/-! # No original atom or ancestor pivot repeats within a reconstructed product -/

namespace Ostmann
open scoped Classical

def WordTransferTemplate.DistinctProducts {A : Type*} :
    {n : ℕ} → WordTransferTemplate A n → Prop
  | 0, .leaf w => w.Nodup
  | _ + 1, .node d l r => d.left.Nodup ∧ d.right.Nodup ∧ l.DistinctProducts ∧ r.DistinctProducts

theorem scheduledHWord_nodup {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (b : Bool)
    (current : CopyScheduleAtoms role (n + 1) → A) (hc : Function.Injective current) :
    (scheduledHWord role n b current).Nodup := by
  apply List.Nodup.map _ (Finset.nodup_toList _)
  intro v w h
  apply Subtype.ext
  exact congrArg Prod.snd (Sum.inl.inj (congrArg Subtype.val (hc h)))

theorem scheduled_reverse_source_after {I A : Type*} (role : I → CopyScheduleRole)
    (depth n : ℕ) (hn : n ≤ depth) (b : Bool) (path : List Bool)
    (current : CopyScheduleAtoms role (n + 1) → ExpandedScheduledVariable A depth)
    (hc : ∀ v, ExpandedCoordinateAfter (n + 1) (current v)) :
    ∀ v, ExpandedCoordinateAfter n
      (reverseCopyLabelMap role n b (expandedPivotAddress A depth n path) current v) := by
  intro v
  unfold reverseCopyLabelMap
  split_ifs
  · exact (hc _).mono (Nat.le_succ n)
  · exact expandedPivotAddress_after A depth n hn path
  · exact (hc _).mono (Nat.le_succ n)

/-- The exact finite pivot addresses are fresh, and a single grouped pivot
atom is inserted at each node. Thus the products use sets of ancestor pivots. -/
theorem scheduledWordTemplate_distinctProducts {I A : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (depth n : ℕ) (hn : n ≤ depth)
    (hu : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b)
    (path : List Bool) (current : CopyScheduleAtoms role n → ExpandedScheduledVariable A depth)
    (hinj : Function.Injective current) (hafter : ∀ v, ExpandedCoordinateAfter n (current v)) :
    (scheduledWordTemplate role (expandedPivotAddress A depth) childBound pivotBound n path current).DistinctProducts := by
  induction n generalizing path with
  | zero =>
    exact List.Nodup.map hinj (Finset.nodup_toList _)
  | succ n ih =>
    have hn' : n ≤ depth := by omega
    have hu' : ∀ j < n, ∀ a b, role a = .pivot j → role b = .pivot j → a = b :=
      fun j hj => hu j (by omega)
    have hs (b : Bool) : Function.Injective
        (reverseCopyLabelMap role n b (expandedPivotAddress A depth n path) current) :=
      reverseCopyLabelMap_injective role n b (hu n (by omega)) _ current hinj
        (fun v => expandedPivotAddress_fresh hn' path (current v) (hafter v))
    exact ⟨scheduledHWord_nodup role n true current hinj,
      scheduledHWord_nodup role n false current hinj,
      ih hn' hu' (true :: path) _ (hs true)
        (scheduled_reverse_source_after role depth n hn' true path current hafter),
      ih hn' hu' (false :: path) _ (hs false)
        (scheduled_reverse_source_after role depth n hn' false path current hafter)⟩

end Ostmann

end OAI
