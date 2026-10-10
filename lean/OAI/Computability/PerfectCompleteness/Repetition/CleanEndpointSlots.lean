import OAI.Computability.PerfectCompleteness.Construction.SourceQuestionReconstruction
import OAI.Computability.PerfectCompleteness.Foundations.CutSlotAssembly

namespace OAI

section

namespace PerfectCompleteness.CleanEndpointSlots

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open SourceQuestionReconstruction

variable {branch : Nat → Nat} {n h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  (clean : Fin (branch h) → Prop)
  (visible : Visible (E := SourceTuple m t) designated clean)

def leftInside (own : {i : Fin (branch h) // clean i} → Fin t → Fin m) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  fun s k => SourceKeys.slot clauses
    (reconstructLeft designated clean visible own s.1 s.2 k)

def rightInside (projected : Fin (branch h) → Bool)
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin v) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  fun s k => SourceKeys.slot clauses
    (reconstructRight designated clean clauses projected visible own s.1 s.2 k)

omit [NeZero m] in
theorem leftInside_nonclean
    (own other : {i : Fin (branch h) // clean i} → Fin t → Fin m)
    (i : Fin (branch h)) (hi : ¬ clean i) (s : Slots branch h) :
    leftInside clauses designated clean visible own (i, s) =
      leftInside clauses designated clean visible other (i, s) := by
  funext k
  have hn : ¬ (clean i ∧ s = designated i) := fun h => hi h.1
  simp only [leftInside, reconstructLeft, reconstruct, dite_eq_right hn]

omit [NeZero m] in
theorem rightInside_nonclean (projected : Fin (branch h) → Bool)
    (own other : {i : Fin (branch h) // clean i} → Fin t → Fin v)
    (i : Fin (branch h)) (hi : ¬ clean i) (s : Slots branch h) :
    rightInside clauses designated clean visible projected own (i, s) =
      rightInside clauses designated clean visible projected other (i, s) := by
  funext k
  have hn : ¬ (clean i ∧ s = designated i) := fun h => hi h.1
  simp only [rightInside, reconstructRight, reconstruct, dite_eq_right hn]

def leftReference : Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  leftInside clauses designated clean visible (fun _ _ => 0)

def rightReference (projected : Fin (branch h) → Bool) :
    Slots branch (h + 1) → Fin t → MixedSupport.Slot :=
  rightInside clauses designated clean visible projected
    (fun _ _ => (clauses 0).variable 0)

variable (rows repeats : Nat → Nat) (p : Path branch n (h + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)

def leftSlots (own : {i : Fin (branch h) // clean i} → Fin t → Fin m) :=
  CutSlotAssembly.fill p outside (leftInside clauses designated clean visible own)

def rightSlots (projected : Fin (branch h) → Bool)
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin v) :=
  CutSlotAssembly.fill p outside (rightInside clauses designated clean visible projected own)

omit [NeZero m] in
theorem leftSlots_kept_eq
    (own other : {i : Fin (branch h) // clean i} → Fin t → Fin m)
    (s : Slots branch n) (hs : CutSamplerKeyLocality.keptLeaf p clean s) :
    leftSlots clauses designated clean visible p outside own s =
      leftSlots clauses designated clean visible p outside other s :=
  CutSlotAssembly.fill_kept_eq p outside _ _ clean
    (leftInside_nonclean clauses designated clean visible own other) s hs

omit [NeZero m] in
theorem rightSlots_kept_eq (projected : Fin (branch h) → Bool)
    (own other : {i : Fin (branch h) // clean i} → Fin t → Fin v)
    (s : Slots branch n) (hs : CutSamplerKeyLocality.keptLeaf p clean s) :
    rightSlots clauses designated clean visible p outside projected own s =
      rightSlots clauses designated clean visible p outside projected other s :=
  CutSlotAssembly.fill_kept_eq p outside _ _ clean
    (rightInside_nonclean clauses designated clean visible projected own other) s hs

def leftReplay
    (record : WholeCutReplay.Tape rows repeats p
      (CutSlotAssembly.fill p outside (leftReference clauses designated clean visible)) clean)
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin m) :
    WholeCutReplay.Tape rows repeats p
      (leftSlots clauses designated clean visible p outside own) clean :=
  CutSlotAssembly.transport rows repeats p outside
    (leftReference clauses designated clean visible)
    (leftInside clauses designated clean visible own) clean
    (leftInside_nonclean clauses designated clean visible (fun _ _ => 0) own) record

def rightReplay (projected : Fin (branch h) → Bool)
    (record : WholeCutReplay.Tape rows repeats p
      (CutSlotAssembly.fill p outside
        (rightReference clauses designated clean visible projected)) clean)
    (own : {i : Fin (branch h) // clean i} → Fin t → Fin v) :
    WholeCutReplay.Tape rows repeats p
      (rightSlots clauses designated clean visible p outside projected own) clean :=
  CutSlotAssembly.transport rows repeats p outside
    (rightReference clauses designated clean visible projected)
    (rightInside clauses designated clean visible projected own) clean
    (rightInside_nonclean clauses designated clean visible projected
      (fun _ _ => (clauses 0).variable 0) own) record

end
end PerfectCompleteness.CleanEndpointSlots

end

end OAI
