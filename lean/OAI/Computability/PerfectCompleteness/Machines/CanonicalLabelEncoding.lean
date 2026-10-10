import OAI.Computability.PerfectCompleteness.Foundations.KeyFiniteness
import OAI.Computability.PerfectCompleteness.Machines.FiniteBlockMachineLemmas

namespace OAI

section

namespace PerfectCompleteness.CanonicalLabelEncoding

open CanonicalKeys CanonicalKeyEncoding
open scoped Classical

noncomputable section

def labelIndex {n : Nat} (key : Key n) : KeyLabel key ↪ Fin (partitionWidth n) where
  toFun label := partEnum n label.val
  inj' := by
    intro a b h
    exact Subtype.ext ((partEnum n).injective h)

def labelEmbedding {n q : Nat} (key : Key n) (large : partitionWidth n ≤ q) :
    KeyLabel key ↪ Fin q :=
  (labelIndex key).trans (Fin.castLEEmb large)

@[simp] theorem labelEmbedding_val {n q : Nat} (key : Key n)
    (large : partitionWidth n ≤ q) (label : KeyLabel key) :
    (labelEmbedding key large label).val = (partEnum n label.val).val := rfl

theorem labelIndex_eq_iff {n : Nat} {left right : Key n}
    (a : KeyLabel left) (b : KeyLabel right) :
    labelIndex left a = labelIndex right b ↔ a.val = b.val :=
  (partEnum n).injective.eq_iff

def paddedMask {n q : Nat} (key : Key n) (a : Fin q) : Bool :=
  if h : a.val < partitionWidth n then partitionMask key.partition ⟨a.val, h⟩ else false

theorem paddedMask_eq_true_iff {n q : Nat} (key : Key n)
    (large : partitionWidth n ≤ q) (a : Fin q) :
    paddedMask key a = true ↔ a ∈ Set.range (labelEmbedding key large) := by
  by_cases h : a.val < partitionWidth n
  · rw [paddedMask, dite_eq_left h]
    change decide ((partEnum n).symm ⟨a.val, h⟩ ∈ key.partition) = true ↔ _
    rw [decide_eq_true_iff]
    constructor
    · intro hpart
      refine ⟨⟨(partEnum n).symm ⟨a.val, h⟩, hpart⟩, ?_⟩
      apply Fin.ext
      simp only [labelEmbedding_val, Equiv.apply_symm_apply]
    · rintro ⟨label, heq⟩
      have hi : partEnum n label.val = (⟨a.val, h⟩ : Fin (partitionWidth n)) := by
        apply Fin.ext
        exact congrArg (fun x : Fin q => x.val) heq
      simpa only [← hi, Equiv.symm_apply_apply] using label.property
  · rw [paddedMask, dite_eq_right h]
    constructor
    · simp
    · rintro ⟨label, heq⟩
      have hval : (partEnum n label.val).val = a.val := congrArg (fun x : Fin q => x.val) heq
      exact (h (hval ▸ (partEnum n label.val).isLt)).elim

theorem label_card_le {n : Nat} (key : Key n) [Fintype (KeyLabel key)] :
    Fintype.card (KeyLabel key) ≤ partitionWidth n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (labelIndex key)
    (labelIndex key).injective

theorem labelIndex_projection {n : Nat} {Y : Type*} (side : Side)
    {slots projected : Fin n → MixedSupport.Slot}
    (p : ∀ i, MixedSupport.Projection (slots i) (projected i))
    (f : MixedSupport.Assignment projected → Y)
    (label : CanonicalKeys.Label slots (f ∘ MixedSupport.projectionMap p)) :
    labelIndex (CanonicalKeys.key side slots (f ∘ MixedSupport.projectionMap p)) label =
      labelIndex (CanonicalKeys.key side projected f) (CanonicalKeys.transportLabel p f label) :=
  rfl

end
end PerfectCompleteness.CanonicalLabelEncoding

end

end OAI
