import OAI.NumberTheory.Ostmann.Characters.AnchorMatchingCount
import OAI.NumberTheory.Ostmann.Construction.ScheduledTreeBulkCoordinates
import OAI.NumberTheory.Ostmann.Construction.PrimeMatchingSupport

namespace OAI

/-! # Code-preserving matchings of the actual scheduled bulk slots -/

namespace Ostmann
open scoped Classical

noncomputable def scheduledBulkAnchorCode (n : ℕ) {m : ℕ}
    (x : Fin (2 ^ n) × Fin m) : Fin n → ℤ × ℤ :=
  finiteAnchorCode (fun _ => 1) (scheduledPathEnumeration n x.1)

/-- This is the code of the actual leaf path, independent of its labeled
position inside that leaf. -/
def PreservesScheduledAnchorCode {I : Type*} (role : I → CopyScheduleRole)
    (n m : ℕ) (word : Fin m ≃ {i : I // role i = .word})
    (e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n)) : Prop :=
  ∀ x, scheduledBulkAnchorCode n
    (separatedMatchingLeft (scheduledSeparatedMatching role n m word e) x) =
      scheduledBulkAnchorCode n x

theorem card_scheduled_bulk_anchor_matching (n m : ℕ) :
    Fintype.card (PartitionMatching (@scheduledBulkAnchorCode n m)
      (@scheduledBulkAnchorCode n m)) ≤ (2 * m) ^ (2 ^ n * m) := by
  let g := (scheduledPathEnumeration n).prodCongr (Equiv.refl (Fin m))
  let f : PartitionMatching (@scheduledBulkAnchorCode n m) (@scheduledBulkAnchorCode n m) →
      PartitionMatching (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode (fun _ => 1) x.1)
        (fun x : (Fin n → Bool) × Fin m => finiteAnchorCode (fun _ => 1) x.1) :=
    fun e => ⟨(g.symm.trans e.val).trans g, by
      intro x
      have h := e.property (g.symm x)
      simpa [scheduledBulkAnchorCode, g] using h⟩
  have hf : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have h := congrArg (fun z => g.symm (z.val (g x))) he
    simpa only [f, Equiv.trans_apply, Equiv.symm_apply_apply] using h
  exact (Fintype.card_le_of_injective f hf).trans
    (card_anchor_matching_le (fun _ => 1) (fun _ => Or.inl rfl))

theorem scheduled_anchor_matching_count {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) :
    Fintype.card {e : PartitionMatching (scheduledBulkLabel role n)
      (scheduledBulkLabel role n) // PreservesScheduledAnchorCode role n m word e} ≤
      (2 * m) ^ (2 ^ n * m) * (Fintype.card (ScheduledNonbulkH role n)).factorial := by
  let f : {e : PartitionMatching (scheduledBulkLabel role n) (scheduledBulkLabel role n) //
      PreservesScheduledAnchorCode role n m word e} →
      PartitionMatching (@scheduledBulkAnchorCode n m) (@scheduledBulkAnchorCode n m) ×
        Equiv.Perm (ScheduledNonbulkH role n) :=
    fun e => (⟨separatedMatchingLeft (scheduledSeparatedMatching role n m word e.val), e.property⟩,
      separatedMatchingRight (scheduledSeparatedMatching role n m word e.val))
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    apply scheduledSeparatedMatching_injective role n m word
    apply separatedMatching_pair_injective
    have hl : separatedMatchingLeft (scheduledSeparatedMatching role n m word e.val) =
        separatedMatchingLeft (scheduledSeparatedMatching role n m word e'.val) :=
      congrArg (fun z => z.1.val) h
    have hr : separatedMatchingRight (scheduledSeparatedMatching role n m word e.val) =
        separatedMatchingRight (scheduledSeparatedMatching role n m word e'.val) :=
      congrArg Prod.snd h
    exact Prod.ext hl hr
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_perm] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (card_scheduled_bulk_anchor_matching n m))

noncomputable def scheduledAnchorMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) : Finset (Equiv.Perm (CopyScheduleH role n)) :=
  Finset.univ.image (fun e : {e : PartitionMatching (scheduledBulkLabel role n)
    (scheduledBulkLabel role n) // PreservesScheduledAnchorCode role n m word e} => e.val.val)

theorem scheduledAnchorMatchingSet_card_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) :
    (scheduledAnchorMatchingSet role n m word).card ≤
      (2 * m) ^ (2 ^ n * m) * (Fintype.card (ScheduledNonbulkH role n)).factorial :=
  (Finset.card_image_le.trans_eq (by simp)).trans (scheduled_anchor_matching_count role n m word)

@[simp] theorem mem_scheduledAnchorMatchingSet {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) (e : Equiv.Perm (CopyScheduleH role n)) :
    e ∈ scheduledAnchorMatchingSet role n m word ↔
      ∃ h : ∀ x, scheduledBulkLabel role n (e x) = scheduledBulkLabel role n x,
        PreservesScheduledAnchorCode role n m word ⟨e, h⟩ := by
  simp only [scheduledAnchorMatchingSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨f, hf⟩, hc⟩, rfl⟩
    exact ⟨hf, hc⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨⟨e, h⟩, hc⟩, rfl⟩

theorem scheduledAnchorMatchingSet_subset {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n m : ℕ)
    (word : Fin m ≃ {i : I // role i = .word}) :
    scheduledAnchorMatchingSet role n m word ⊆ cellPreservingMatchings (scheduledBulkLabel role n) := by
  intro e he
  obtain ⟨h, _⟩ := (mem_scheduledAnchorMatchingSet role n m word e).mp he
  exact (mem_cellPreservingMatchings _ _).mpr h

end Ostmann

end OAI
