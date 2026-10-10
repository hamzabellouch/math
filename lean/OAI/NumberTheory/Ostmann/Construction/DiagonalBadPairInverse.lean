import OAI.NumberTheory.Ostmann.Construction.DiagonalCounterpartReindexBands

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Construction

theorem reconstructCounterpart_compatible_inverse (sources : SourceFamily)
    (T : List SourceSlot) (giant : PrimeSource) (x : RemainingSample sources T giant)
    (e : Equiv.Perm (RemainingIndex T)) (he : CounterpartCompatible sources T giant x e) :
    CounterpartCompatible sources T giant (reconstructCounterpart sources T giant x e he) e.symm := by
  intro i
  simpa only [reconstructCounterpart_coordinate,Equiv.apply_symm_apply] using
    remainingCoordinate_mem sources T giant x i

@[simp] theorem reconstructCounterpart_inverse (sources : SourceFamily)
    (T : List SourceSlot) (giant : PrimeSource) (x : RemainingSample sources T giant)
    (e : Equiv.Perm (RemainingIndex T)) (he : CounterpartCompatible sources T giant x e) :
    reconstructCounterpart sources T giant (reconstructCounterpart sources T giant x e he)
      e.symm (reconstructCounterpart_compatible_inverse sources T giant x e he)=x := by
  apply remainingCoordinate_ext sources T giant
  intro i
  simp only [reconstructCounterpart_coordinate,Equiv.apply_symm_apply]

lemma PreservesRemainingBands.symm {T : List SourceSlot} {e : Equiv.Perm (RemainingIndex T)}
    (he : PreservesRemainingBands T e) : PreservesRemainingBands T e.symm := by
  intro i
  simpa only [Equiv.apply_symm_apply] using (he (e.symm i)).symm

abbrev BadCounterpartPair (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (B : Equiv.Perm (RemainingIndex T) → Prop) :=
  {z : RemainingSample sources T giant × Equiv.Perm (RemainingIndex T) //
    CounterpartCompatible sources T giant z.1 z.2 ∧ B z.2}

def badCounterpartSwap (sources : SourceFamily) (T : List SourceSlot) (giant : PrimeSource)
    (B : Equiv.Perm (RemainingIndex T) → Prop) (hB : ∀e,B e → B e.symm)
    (z : BadCounterpartPair sources T giant B) : BadCounterpartPair sources T giant B :=
  ⟨(reconstructCounterpart sources T giant z.val.1 z.val.2 z.property.1,z.val.2.symm),
    reconstructCounterpart_compatible_inverse sources T giant z.val.1 z.val.2 z.property.1,
    hB z.val.2 z.property.2⟩

theorem badCounterpartSwap_involutive (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (B : Equiv.Perm (RemainingIndex T) → Prop)
    (hB : ∀e,B e → B e.symm) : Function.Involutive (badCounterpartSwap sources T giant B hB) := by
  intro z
  apply Subtype.ext
  apply Prod.ext
  · exact reconstructCounterpart_inverse sources T giant z.val.1 z.val.2 z.property.1
  · exact Equiv.symm_symm _

def badCounterpartSwapEquiv (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (B : Equiv.Perm (RemainingIndex T) → Prop)
    (hB : ∀e,B e → B e.symm) :
    BadCounterpartPair sources T giant B ≃ BadCounterpartPair sources T giant B :=
  { toFun := badCounterpartSwap sources T giant B hB
    invFun := badCounterpartSwap sources T giant B hB
    left_inv := badCounterpartSwap_involutive sources T giant B hB
    right_inv := badCounterpartSwap_involutive sources T giant B hB }

end Ostmann.Construction

end

end OAI
