import OAI.Computability.PerfectCompleteness.Construction.LocalCompletionFamily
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalCoarseningErasure

namespace OAI

section

namespace PerfectCompleteness.CanonicalPartialTable

open MixedSupport CanonicalKeys CanonicalKeyShape CanonicalEdges CanonicalLabelEncoding
open scoped Classical

noncomputable section

abbrev Input (n k l : Nat) :=
  Σ shapes : Fin n → Shape,
    (Assignment (dummySlots shapes) → Fin k) × (Fin k → Fin l)

instance inputFintype (n k l : Nat) : Fintype (Input n k l) := by
  unfold Input
  infer_instance

variable {n k l q : Nat}

def slots (data : Input n k l) : Fin n → Slot := dummySlots data.1

def joint (data : Input n k l) : Assignment (slots data) → Fin k := data.2.1

def outputMap (data : Input n k l) : Fin k → Fin l := data.2.2

def leftKey (data : Input n k l) : Key n := key .left (slots data) (joint data)

def rightKey (data : Input n k l) : Key n :=
  key .right (slots data) (outputMap data ∘ joint data)

theorem left_large (large : CanonicalKeyEncoding.partitionWidth n ≤ q) :
    CanonicalKeyEncoding.partitionWidth n ≤ 2 * q := by omega

def leftEmbedding (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) : Label (slots data) (joint data) ↪ Fin (2 * q) :=
  labelEmbedding (leftKey data) (left_large large)

def rightEmbedding (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) : Label (slots data) (outputMap data ∘ joint data) ↪ Fin q :=
  labelEmbedding (rightKey data) large

def image (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (a : Fin (2 * q)) : Fin q :=
  if h : a ∈ Set.range (leftEmbedding large data) then
    rightEmbedding large data
      (coarsen (slots data) (joint data) (outputMap data) h.choose)
  else ⟨0, hq⟩

def lookup (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) : LocalCompletionFamily.Input q :=
  (paddedMask (leftKey data), image hq large data)

@[simp] theorem lookup_mask (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q) (data : Input n k l) :
    (lookup hq large data).1 = paddedMask (leftKey data) := rfl

theorem mask_true (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (a : Fin (2 * q)) :
    (lookup hq large data).1 a = true ↔ a ∈ Set.range (leftEmbedding large data) :=
  paddedMask_eq_true_iff (leftKey data) (left_large large) a

theorem image_legal (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (P : Label (slots data) (joint data)) :
    (lookup hq large data).2 (leftEmbedding large data P) =
      rightEmbedding large data (coarsen (slots data) (joint data) (outputMap data) P) := by
  have h : leftEmbedding large data P ∈ Set.range (leftEmbedding large data) := ⟨P, rfl⟩
  have hchosen : h.choose = P := (leftEmbedding large data).injective h.choose_spec
  change image hq large data (leftEmbedding large data P) = _
  rw [image, dite_eq_left h, hchosen]

theorem image_illegal (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (a : Fin (2 * q))
    (hillegal : (lookup hq large data).1 a ≠ true) :
    (lookup hq large data).2 a = ⟨0, hq⟩ := by
  have h : a ∉ Set.range (leftEmbedding large data) := by
    intro ha
    exact hillegal ((mask_true hq large data a).2 ha)
  exact dite_eq_right h

def legalEquiv (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) :
    Label (slots data) (joint data) ≃ LocalCompletionFamily.Legal (lookup hq large data) where
  toFun P := ⟨leftEmbedding large data P,
    (mask_true hq large data _).2 ⟨P, rfl⟩⟩
  invFun a := ((mask_true hq large data a.val).1 a.property).choose
  left_inv P := (leftEmbedding large data).injective
    ((mask_true hq large data _).1
      ((mask_true hq large data _).2 ⟨P, rfl⟩)).choose_spec
  right_inv a := Subtype.ext ((mask_true hq large data a.val).1 a.property).choose_spec

@[simp] theorem legalEquiv_val (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l) (P : Label (slots data) (joint data)) :
    (legalEquiv hq large data P).val = leftEmbedding large data P := rfl

theorem admissible (hq : 0 < q) (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (data : Input n k l)
    (hsmall : ∀ Q, Nat.card {P : Label (slots data) (joint data) //
      coarsen (slots data) (joint data) (outputMap data) P = Q} ≤ 2) :
    LocalCompletionFamily.Admissible (lookup hq large data) := by
  let : Fintype (Label (slots data) (joint data)) := Fintype.ofFinite _
  intro b
  let fibers :
      {P : Label (slots data) (joint data) // rightEmbedding large data
        (coarsen (slots data) (joint data) (outputMap data) P) = b} ≃
      {a : LocalCompletionFamily.Legal (lookup hq large data) //
        (lookup hq large data).2 a.val = b} :=
    (legalEquiv hq large data).subtypeEquiv (fun P => by
      rw [legalEquiv_val, image_legal])
  have hcard := Nat.card_congr fibers
  have hbound := CompletionSoundness.LegalProjectionGame.embedded_fiber_le_two
    (rightEmbedding large data) (coarsen (slots data) (joint data) (outputMap data))
    (by intro Q; simpa only [← Nat.card_eq_fintype_card] using hsmall Q) b
  simp only [← Nat.card_eq_fintype_card] at hcard hbound ⊢
  exact hcard.symm.le.trans hbound

theorem admissible_of_output_fibers (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q) (data : Input n k l)
    (hsmall : ∀ b, Nat.card {a : Fin k // outputMap data a = b} ≤ 2) :
    LocalCompletionFamily.Admissible (lookup hq large data) :=
  admissible hq large data
    (coarsen_at_most_two (slots data) (joint data) (outputMap data) hsmall)

def input (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) : Input n k l :=
  ⟨shape sourceSlots, transport sourceSlots f, p⟩

@[simp] theorem leftEmbedding_input (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) (P : Label sourceSlots f) :
    leftEmbedding large (input sourceSlots f p)
        (CanonicalCoarseningErasure.transportLabel sourceSlots f P) =
      labelEmbedding (key .left sourceSlots f) (left_large large) P := rfl

theorem lookup_mask_actual (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) :
    (lookup hq large (input sourceSlots f p)).1 = paddedMask (key .left sourceSlots f) := by
  funext a
  change paddedMask (key .left (dummySlots (shape sourceSlots)) (transport sourceSlots f)) a = _
  simp only [paddedMask, key, ← partition_erasure sourceSlots f]

theorem mask_actual_true (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) (a : Fin (2 * q)) :
    (lookup hq large (input sourceSlots f p)).1 a = true ↔
      a ∈ Set.range (labelEmbedding (key .left sourceSlots f) (left_large large)) := by
  rw [lookup_mask_actual]
  exact paddedMask_eq_true_iff (key .left sourceSlots f) (left_large large) a

theorem image_actual_legal (hq : 0 < q)
    (large : CanonicalKeyEncoding.partitionWidth n ≤ q)
    (sourceSlots : Fin n → Slot) (f : Assignment sourceSlots → Fin k)
    (p : Fin k → Fin l) (P : Label sourceSlots f) :
    (lookup hq large (input sourceSlots f p)).2
        (labelEmbedding (key .left sourceSlots f) (left_large large) P) =
      labelEmbedding (key .right sourceSlots (p ∘ f)) large (coarsen sourceSlots f p P) := by
  have h := image_legal hq large (input sourceSlots f p)
    (CanonicalCoarseningErasure.transportLabel sourceSlots f P)
  rw [leftEmbedding_input] at h
  refine h.trans ?_
  apply Fin.ext
  change (CanonicalKeyEncoding.partEnum n
    (coarsen (dummySlots (shape sourceSlots)) (transport sourceSlots f) p
      (CanonicalCoarseningErasure.transportLabel sourceSlots f P)).val).val =
    (CanonicalKeyEncoding.partEnum n (coarsen sourceSlots f p P).val).val
  exact congrArg (fun a : Fin (CanonicalKeyEncoding.partitionWidth n) => a.val)
    (CanonicalCoarseningErasure.partIndex_coarsen sourceSlots f p P).symm

end
end PerfectCompleteness.CanonicalPartialTable

end

end OAI
