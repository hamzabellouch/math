import OAI.Computability.PerfectCompleteness.Machines.StoppedOwnInputGeometry
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalProjectedMeeting

namespace OAI

section

namespace PerfectCompleteness.StoppedCleanOwnInputGeometry

noncomputable section

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

abbrev F2 := ZMod 2

variable {branch : Nat → Nat} {n t : Nat} (rows repeats : Nat → Nat)

theorem pathTapeEquiv_heq
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (hp : p = q)
    (tape : WholeArraySampler.Tape rows repeats p.2 slots) :
    HEq (StoppedOwnInputGeometry.pathTapeEquiv rows repeats slots hp tape) tape :=
  cast_heq _ _

theorem uncastTape_heq
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    {k : Nat} (hk : Nodes.height lower = k)
    (tape : WholeArraySampler.Tape rows repeats
      ((Nodes.path upper).append (hk ▸ cut.path)) slots) :
    HEq (CleanPhysicalDecoderLaw.uncastTape slots upper lower cut hk tape) tape := by
  cases hk
  rfl

variable (slots target : Slots branch n → Fin t → MixedSupport.Slot)
  (hslots : slots = target) (upper lower otherLower : Nodes branch n)
  (hlower : lower = otherLower)
  (cut : OwnInputReference.Cut upper lower)
  (otherCut : OwnInputReference.Cut upper otherLower) (hcut : HEq cut otherCut)
  (W : Submodule F2 (Block rows upper))
  (tape : WholeArraySampler.Tape rows repeats
    (WholeArrayInteriorOwnInputLaw.fullPath upper lower cut) slots)
  (otherTape : WholeArraySampler.Tape rows repeats
    (WholeArrayInteriorOwnInputLaw.fullPath upper otherLower otherCut) target)
  (htape : HEq tape otherTape)

include hslots hlower hcut htape

theorem exposedRead_heq :
    HEq (WholeArrayInteriorOwnInputLaw.exposedRead rows repeats slots upper lower cut W tape)
      (WholeArrayInteriorOwnInputLaw.exposedRead rows repeats target upper otherLower
        otherCut W otherTape) := by
  cases hslots
  cases hlower
  have hc : cut = otherCut := eq_of_heq hcut
  cases hc
  have ht : tape = otherTape := eq_of_heq htape
  cases ht
  rfl

theorem visibleRead_heq :
    HEq (WholeArrayInteriorOwnInputLaw.exposedRead rows repeats slots upper lower cut W tape).2
      (WholeArrayInteriorOwnInputLaw.exposedRead rows repeats target upper otherLower
        otherCut W otherTape).2 := by
  cases hslots
  cases hlower
  have hc : cut = otherCut := eq_of_heq hcut
  cases hc
  have ht : tape = otherTape := eq_of_heq htape
  cases ht
  rfl

end
end PerfectCompleteness.StoppedCleanOwnInputGeometry

end

end OAI
