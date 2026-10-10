import OAI.Computability.PerfectCompleteness.Repetition.CleanCountingLemmas

namespace OAI

section

namespace PerfectCompleteness.RetainedKeyTransport

open MixedSupport CanonicalKeys CleanKeyErasure CleanKeyFactorization
open scoped Classical

noncomputable section

variable {n : Nat} {Y : Type*}

theorem retainedSlots_eq (slots target : Fin n → Slot) (keep : Fin n → Prop)
    (hs : ∀ i, keep i → slots i = target i) :
    retainedSlots slots keep = retainedSlots target keep := by
  funext i
  exact hs i.val i.property

def retainedAssignmentEquiv (slots target : Fin n → Slot) (keep : Fin n → Prop)
    (hs : ∀ i, keep i → slots i = target i) :
    Assignment (retainedSlots slots keep) ≃ Assignment (retainedSlots target keep) :=
  Equiv.cast (congrArg Assignment (retainedSlots_eq slots target keep hs))

private theorem assignment_cast_apply {I : Type*} {a b : I → Slot} (h : a = b)
    (x : Assignment a) (i : I) :
    (Equiv.cast (congrArg Assignment h) x) i =
      cast (congrArg Slot.Domain (congrFun h i)) (x i) := by
  cases h
  rfl

theorem retainedAssignmentEquiv_apply (slots target : Fin n → Slot) (keep : Fin n → Prop)
    (hs : ∀ i, keep i → slots i = target i)
    (x : Assignment (retainedSlots slots keep)) (i : {i : Fin n // keep i}) :
    retainedAssignmentEquiv slots target keep hs x i =
      cast (congrArg Slot.Domain (hs i.val i.property)) (x i) :=
  assignment_cast_apply (retainedSlots_eq slots target keep hs) x i

theorem retainedAssignmentEquiv_agree_heq
    (slots target : Fin n → Slot) (keep : Fin n → Prop)
    (hs : ∀ i, keep i → slots i = target i)
    (x : Assignment slots) (y : Assignment target)
    (hret : retainedAssignmentEquiv slots target keep hs (retain slots keep x) =
      retain target keep y) (i : Fin n) (hi : keep i) : HEq (x i) (y i) := by
  have hcoord := congrFun hret ⟨i, hi⟩
  rw [retainedAssignmentEquiv_apply] at hcoord
  exact (cast_heq (congrArg Slot.Domain (hs i hi)) (x i)).symm.trans
    (heq_of_eq hcoord)

theorem exists_retained_factor
    (slots target : Fin n → Slot) (keep : Fin n → Prop)
    (hs : ∀ i, keep i → slots i = target i)
    (f : Assignment slots → Y) (g : Assignment target → Y)
    (hagree : ∀ x y,
      retainedAssignmentEquiv slots target keep hs (retain slots keep x) =
        retain target keep y → f x = g y) :
    ∃ h : Assignment (retainedSlots target keep) → Y,
      f = (h ∘ retainedAssignmentEquiv slots target keep hs) ∘ retain slots keep ∧
        g = h ∘ retain target keep := by
  refine ⟨fun u => g (fill target keep u), ?_, ?_⟩
  · funext x
    exact hagree x
      (fill target keep (retainedAssignmentEquiv slots target keep hs (retain slots keep x)))
      (retain_fill target keep _).symm
  · funext y
    let x := fill slots keep
      ((retainedAssignmentEquiv slots target keep hs).symm (retain target keep y))
    have hx : retainedAssignmentEquiv slots target keep hs (retain slots keep x) =
        retain target keep y := by
      dsimp only [x]
      rw [retain_fill, Equiv.apply_symm_apply]
    exact (hagree x y hx).symm.trans
      (hagree x (fill target keep (retain target keep y))
        (hx.trans (retain_fill target keep _).symm))

private theorem retainedKey_cast (side : Side) (keep : Fin n → Prop)
    {a b : {i : Fin n // keep i} → Slot} (h : a = b) (g : Assignment b → Y) :
    retainedKey side keep a (g ∘ Equiv.cast (congrArg Assignment h)) =
      retainedKey side keep b g := by
  cases h
  rfl

private theorem retainedResponse_cast (labeling : KeyStrategy.Strategy n)
    (side : Side) (keep : Fin n → Prop)
    {a b : {i : Fin n // keep i} → Slot} (h : a = b) (g : Assignment b → Y) :
    retainedResponse labeling side keep a (g ∘ Equiv.cast (congrArg Assignment h)) =
      retainedResponse labeling side keep b g := by
  cases h
  rfl

theorem key_eq (side : Side) (slots target : Fin n → Slot) (keep : Fin n → Prop)
    (hs : ∀ i, keep i → slots i = target i)
    (f : Assignment slots → Y) (g : Assignment target → Y)
    (hagree : ∀ x y,
      retainedAssignmentEquiv slots target keep hs (retain slots keep x) =
        retain target keep y → f x = g y) :
    CanonicalKeys.key side slots f = CanonicalKeys.key side target g := by
  obtain ⟨h, hf, hg⟩ := exists_retained_factor slots target keep hs f g hagree
  calc
    _ = retainedKey side keep (retainedSlots slots keep)
        (h ∘ retainedAssignmentEquiv slots target keep hs) := by
      rw [hf]
      exact key_factor side slots keep _
    _ = retainedKey side keep (retainedSlots target keep) h :=
      retainedKey_cast side keep (retainedSlots_eq slots target keep hs) h
    _ = _ := by
      rw [hg]
      exact (key_factor side target keep h).symm

theorem label_val_eq (labeling : KeyStrategy.Strategy n) (side : Side)
    (slots target : Fin n → Slot) (keep : Fin n → Prop)
    (hs : ∀ i, keep i → slots i = target i)
    (f : Assignment slots → Y) (g : Assignment target → Y)
    (hagree : ∀ x y,
      retainedAssignmentEquiv slots target keep hs (retain slots keep x) =
        retain target keep y → f x = g y) :
    (KeyStrategy.label labeling side slots f).val =
      (KeyStrategy.label labeling side target g).val :=
  KeyStrategy.label_val_eq_of_key_eq labeling side side slots target f g
    (key_eq side slots target keep hs f g hagree)

theorem response_eq (labeling : KeyStrategy.Strategy n) (side : Side)
    (slots target : Fin n → Slot) (keep : Fin n → Prop)
    (hs : ∀ i, keep i → slots i = target i)
    (f : Assignment slots → Y) (g : Assignment target → Y)
    (hagree : ∀ x y,
      retainedAssignmentEquiv slots target keep hs (retain slots keep x) =
        retain target keep y → f x = g y) :
    KeyStrategy.response labeling side slots f = KeyStrategy.response labeling side target g := by
  obtain ⟨h, hf, hg⟩ := exists_retained_factor slots target keep hs f g hagree
  calc
    _ = retainedResponse labeling side keep (retainedSlots slots keep)
        (h ∘ retainedAssignmentEquiv slots target keep hs) := by
      rw [hf]
      exact response_factor labeling side slots keep _
    _ = retainedResponse labeling side keep (retainedSlots target keep) h :=
      retainedResponse_cast labeling side keep (retainedSlots_eq slots target keep hs) h
    _ = _ := by
      rw [hg]
      exact (response_factor labeling side target keep h).symm

end
end PerfectCompleteness.RetainedKeyTransport

end

end OAI
