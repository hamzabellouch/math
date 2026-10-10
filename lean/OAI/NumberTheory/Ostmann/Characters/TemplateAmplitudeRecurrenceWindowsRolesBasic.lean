import OAI.NumberTheory.Ostmann.Characters.TemplateWords

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem scheduled_role_index_lt (k j : ℕ) (i : (schedule k j).Slot) :
    (∀ r, (schedule k j).role i = .pivot r → r < k) ∧
    (∀ r b, (schedule k j).role i = .anchor r b → r < k) := by
  induction j with
  | zero =>
    rcases i with ⟨r,b⟩
    cases r <;> simp [schedule, initial, InitialRole.role]
  | succ j ih =>
    cases i with
    | inl z => exact ih z.1.val
    | inr z => exact ih z.val

abbrev ScheduledCopiedRoles (k j : ℕ) :=
  WordSlot k j ⊕ ({r : ℕ // r ∈ Finset.Ico (j+1) k} ⊕ Bool)

abbrev ScheduledCopiedSlots (k j : ℕ) :=
  {i : (schedule k j).Slot // (schedule k j).IsCopied j i}

def scheduledCopiedRoleMap (k j : ℕ) (hj : j < k) :
    ScheduledCopiedRoles k j → ScheduledCopiedSlots k j
  | .inl w => ⟨w.val, word_copied _ _ _ w.property.1 w.property.2⟩
  | .inr (.inl r) =>
    let z := (pivotEquiv k j r.val
      (by have := (Finset.mem_Ico.mp r.property).1; omega)
      (Finset.mem_Ico.mp r.property).2).symm PUnit.unit
    ⟨z.val, z.property.1, Or.inr (Or.inl ⟨r.val,
      by have := (Finset.mem_Ico.mp r.property).1; omega, z.property.2⟩)⟩
  | .inr (.inr b) =>
    let z := anchorSlot k j hj b
    ⟨z.val, z.property.1, Or.inr (Or.inr ⟨b,z.property.2⟩)⟩

@[simp] theorem scheduledCopiedRoleMap_word (k j : ℕ) (hj : j < k) (w : WordSlot k j) :
    (schedule k j).role (scheduledCopiedRoleMap k j hj (.inl w)).val = .word :=
  w.property.2

@[simp] theorem scheduledCopiedRoleMap_pivot (k j : ℕ) (hj : j < k)
    (r : {r : ℕ // r ∈ Finset.Ico (j+1) k}) :
    (schedule k j).role (scheduledCopiedRoleMap k j hj (.inr (.inl r))).val = .pivot r.val :=
  ((pivotEquiv k j r.val (by have := (Finset.mem_Ico.mp r.property).1; omega)
    (Finset.mem_Ico.mp r.property).2).symm PUnit.unit).property.2

@[simp] theorem scheduledCopiedRoleMap_anchor (k j : ℕ) (hj : j < k) (b : Bool) :
    (schedule k j).role (scheduledCopiedRoleMap k j hj (.inr (.inr b))).val = .anchor j b :=
  (anchorSlot k j hj b).property.2

theorem scheduledCopiedRoleMap_injective (k j : ℕ) (hj : j < k) :
    Function.Injective (scheduledCopiedRoleMap k j hj) := by
  intro a b hab
  have hr := congrArg (fun i : ScheduledCopiedSlots k j => (schedule k j).role i.val) hab
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  · exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : ScheduledCopiedSlots k j => z.val) hab))
  · simp only [scheduledCopiedRoleMap_word, scheduledCopiedRoleMap_pivot] at hr
    contradiction
  · simp only [scheduledCopiedRoleMap_word, scheduledCopiedRoleMap_anchor] at hr
    contradiction
  · simp only [scheduledCopiedRoleMap_word, scheduledCopiedRoleMap_pivot] at hr
    contradiction
  · simp only [scheduledCopiedRoleMap_pivot] at hr
    exact congrArg (fun r => Sum.inr (Sum.inl r)) (Subtype.ext (Role.pivot.inj hr))
  · simp only [scheduledCopiedRoleMap_pivot, scheduledCopiedRoleMap_anchor] at hr
    contradiction
  · simp only [scheduledCopiedRoleMap_word, scheduledCopiedRoleMap_anchor] at hr
    contradiction
  · simp only [scheduledCopiedRoleMap_pivot, scheduledCopiedRoleMap_anchor] at hr
    contradiction
  · simp only [scheduledCopiedRoleMap_anchor] at hr
    exact congrArg (fun b => Sum.inr (Sum.inr b)) (Role.anchor.inj hr).2

theorem scheduledCopiedRoleMap_surjective (k j : ℕ) (hj : j < k) :
    Function.Surjective (scheduledCopiedRoleMap k j hj) := by
  intro i
  rcases i.property.2 with hw | ⟨r,hjr,hr⟩ | ⟨b,hb⟩
  · exact ⟨.inl ⟨i.val,i.property.1,hw⟩,rfl⟩
  · have hrk := (scheduled_role_index_lt k j i.val).1 r hr
    let r' : {r : ℕ // r ∈ Finset.Ico (j+1) k} := ⟨r,Finset.mem_Ico.mpr ⟨by omega,hrk⟩⟩
    refine ⟨.inr (.inl r'), ?_⟩
    apply Subtype.ext
    have hz : (pivotEquiv k j r (by omega) hrk).symm PUnit.unit =
        ⟨i.val,i.property.1,hr⟩ := by
      apply (pivotEquiv k j r (by omega) hrk).injective
      exact Subsingleton.elim _ _
    exact congrArg (fun z : {i : (schedule k j).Slot // (schedule k j).IsPivot r i} => z.val) hz
  · refine ⟨.inr (.inr b), ?_⟩
    apply Subtype.ext
    have hz : anchorSlot k j hj b = ⟨i.val,i.property.1,hb⟩ := by
      apply (anchorEquiv k j j le_rfl hj b).injective
      exact Subsingleton.elim _ _
    exact congrArg (fun z : {i : (schedule k j).Slot // (schedule k j).eligible i ∧ (schedule k j).role i = .anchor j b} => z.val) hz

def scheduledCopiedRoleEquiv (k j : ℕ) (hj : j < k) :
    ScheduledCopiedRoles k j ≃ ScheduledCopiedSlots k j :=
  Equiv.ofBijective (scheduledCopiedRoleMap k j hj)
    ⟨scheduledCopiedRoleMap_injective k j hj, scheduledCopiedRoleMap_surjective k j hj⟩

end Ostmann.Characters.Template

end

end OAI
