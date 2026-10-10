import OAI.Computability.PerfectCompleteness.Decoding.CleanDecoderRateLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CleanPhysicalCanonicalQuery

namespace OAI

section

namespace PerfectCompleteness.CleanNativeReplay

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

section Transport

variable {branch : Nat → Nat} {n h t : Nat}

private theorem transport_target_heq (rows repeats : Nat → Nat)
    (p : Path branch n (h + 1))
    (reference target other : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop) (heq : target = other)
    (hs : ∀ s, CutSamplerKeyLocality.keptLeaf p clean s → reference s = target s)
    (hs' : ∀ s, CutSamplerKeyLocality.keptLeaf p clean s → reference s = other s)
    (tape : WholeCutReplay.Tape rows repeats p reference clean) :
    HEq (WholeCutReplayKeys.transportTape rows repeats p reference target clean hs tape)
      (WholeCutReplayKeys.transportTape rows repeats p reference other clean hs' tape) := by
  cases heq
  rfl

private theorem evaluateArrays_heq (rows repeats : Nat → Nat)
    (p : Path branch n (h + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop) (hs : slots = target)
    (tape : WholeCutReplay.Tape rows repeats p slots clean)
    (other : WholeCutReplay.Tape rows repeats p target clean) (htape : HEq tape other) :
    HEq (WholeCutReplay.evaluateArrays rows repeats p slots clean tape)
      (WholeCutReplay.evaluateArrays rows repeats p target clean other) := by
  cases hs
  cases htape
  rfl

end Transport

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

abbrev context (x : CleanDecoderRate.Sample S) := CleanDecoderPairLaw.context S x
abbrev leftOwn (x : CleanDecoderRate.Sample S) := CleanDecoderPairLaw.leftOwn S x
abbrev rightOwn (x : CleanDecoderRate.Sample S) := CleanDecoderPairLaw.rightOwn S x

abbrev leftSlots (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalCanonicalQuery.leftSlots rows repeats (CleanDecoderRate.path S)
    S.outside S.clauses S.designated x

abbrev rightSlots (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalCanonicalQuery.rightSlots rows repeats (CleanDecoderRate.path S)
    S.outside S.clauses S.designated x

abbrev leftTape (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalReplay.leftTape rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated x S.exterior

abbrev rightTape (x : CleanDecoderRate.Sample S) :=
  CleanPhysicalReplay.rightTape rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated x S.exterior

theorem leftSlots_eq (x : CleanDecoderRate.Sample S) :
    CleanDecoderContext.leftSlots (context S x) (leftOwn S x) = leftSlots S x :=
  CleanRecordDecoderInput.leftSlots_eq rows repeats upper d S.cut S.outside S.placeholder
    S.clauses S.designated (CleanDecoderRate.observations S x) S.exterior x
    (CleanRecordDecoderInput.event_observe rows repeats upper d S.cut S.clauses S.designated x)

theorem rightSlots_eq (x : CleanDecoderRate.Sample S) :
    CleanDecoderContext.rightSlots (context S x) (rightOwn S x) = rightSlots S x :=
  CleanRecordDecoderInput.rightSlots_eq rows repeats upper d S.cut S.outside S.placeholder
    S.clauses S.designated (CleanDecoderRate.observations S x) S.exterior x
    (CleanRecordDecoderInput.event_observe rows repeats upper d S.cut S.clauses S.designated x)

theorem leftReplay_heq (x : CleanDecoderRate.Sample S) :
    HEq (CleanLeftDecoder.replay (CleanDecoderContext.leftExposed (context S x)) (leftOwn S x))
      (WholeCutReplay.erase rows repeats (CleanDecoderRate.path S) (leftSlots S x)
        (context S x).clean (leftTape S x)) := by
  let record := CleanDecoderRate.observations S x
  have hevent := CleanRecordDecoderInput.event_observe
    rows repeats upper d S.cut S.clauses S.designated x
  have hrecord := CleanPhysicalReplay.leftRecord_eq_erase
    rows repeats (CleanDecoderRate.path S) S.outside S.placeholder S.clauses S.designated
    record x hevent S.exterior
  have htransport := transport_target_heq rows repeats (CleanDecoderRate.path S)
    (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside
      (CleanRecordChildBlocks.leftRef rows S.clauses S.designated record))
    (CleanDecoderContext.leftSlots (context S x) (leftOwn S x)) (leftSlots S x)
    (context S x).clean (leftSlots_eq S x)
    (CleanEndpointSlots.leftSlots_kept_eq S.clauses S.designated (context S x).clean
      (context S x).visible (CleanDecoderRate.path S) S.outside (fun _ _ => 0) (leftOwn S x))
    (CutSlotAssembly.fill_kept_eq (CleanDecoderRate.path S) S.outside _ _ _
      (CleanPhysicalReplay.leftInside_nonclean rows repeats (CleanDecoderRate.path S)
        S.clauses S.designated record x hevent))
    (CleanPhysicalReplay.leftRecord rows repeats (CleanDecoderRate.path S)
      S.outside S.placeholder S.clauses S.designated record S.exterior)
  exact htransport.trans (heq_of_eq hrecord)

theorem rightReplay_heq (x : CleanDecoderRate.Sample S) :
    HEq (CleanRightDecoder.replay (context S x).clauses (context S x).designated
      (context S x).clean (context S x).visible (context S x).projected upper
      (CleanDecoderContext.lower (context S x)) (context S x).cut
      (CleanDecoderContext.lowerHeight upper d) (context S x).outside rows repeats
      (context S x).rightTape (rightOwn S x))
      (WholeCutReplay.erase rows repeats (CleanDecoderRate.path S) (rightSlots S x)
        (context S x).clean (rightTape S x)) := by
  let record := CleanDecoderRate.observations S x
  have hevent := CleanRecordDecoderInput.event_observe
    rows repeats upper d S.cut S.clauses S.designated x
  have hrecord := CleanPhysicalReplay.rightRecord_eq_erase
    rows repeats (CleanDecoderRate.path S) S.outside S.placeholder S.clauses S.designated
    record x hevent S.exterior
  have htransport := transport_target_heq rows repeats (CleanDecoderRate.path S)
    (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside
      (CleanRecordChildBlocks.rightRef rows S.clauses S.designated record))
    (CleanDecoderContext.rightSlots (context S x) (rightOwn S x)) (rightSlots S x)
    (context S x).clean (rightSlots_eq S x)
    (CleanEndpointSlots.rightSlots_kept_eq S.clauses S.designated (context S x).clean
      (context S x).visible (CleanDecoderRate.path S) S.outside (context S x).projected
      (fun _ _ => (S.clauses 0).variable 0) (rightOwn S x))
    (CutSlotAssembly.fill_kept_eq (CleanDecoderRate.path S) S.outside _ _ _
      (CleanPhysicalReplay.rightInside_nonclean rows repeats (CleanDecoderRate.path S)
        S.clauses S.designated record x hevent))
    (CleanPhysicalReplay.rightRecord rows repeats (CleanDecoderRate.path S)
      S.outside S.placeholder S.clauses S.designated record S.exterior)
  exact htransport.trans (heq_of_eq hrecord)

variable (cube : Nat) (hcube : 0 < cube)

theorem left_grouped_zero (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    WholeCutZero.GroupedAtClean rows repeats (CleanDecoderRate.path S) (leftSlots S x)
      (context S x).clean (leftTape S x) :=
  CleanPhysicalReplay.leftTape_grouped_zero rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated
    (fun _ => SourceOddLists.tupleLaw m t)
    (fun i => FiniteProduct.law
      (fun _ : {leaf : Slots branch h // leaf ≠ S.designated i} => SourceOddLists.tupleLaw m t))
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)
    (CleanDecoderRate.observations S x) x hx
    (CleanRecordDecoderInput.event_observe rows repeats upper d S.cut S.clauses S.designated x)
    S.exterior

theorem right_grouped_zero (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    WholeCutZero.GroupedAtClean rows repeats (CleanDecoderRate.path S) (rightSlots S x)
      (context S x).clean (rightTape S x) :=
  CleanPhysicalReplay.rightTape_grouped_zero rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated
    (fun _ => SourceOddLists.tupleLaw m t)
    (fun i => FiniteProduct.law
      (fun _ : {leaf : Slots branch h // leaf ≠ S.designated i} => SourceOddLists.tupleLaw m t))
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)
    (CleanDecoderRate.observations S x) x hx
    (CleanRecordDecoderInput.event_observe rows repeats upper d S.cut S.clauses S.designated x)
    S.exterior

theorem leftArrays_heq (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    HEq (CleanLeftDecoder.arrays (CleanDecoderContext.leftExposed (context S x)) (leftOwn S x))
      (WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S) (leftSlots S x)
        (leftTape S x)) := by
  have h := evaluateArrays_heq rows repeats (CleanDecoderRate.path S)
    (CleanDecoderContext.leftSlots (context S x) (leftOwn S x)) (leftSlots S x)
    (context S x).clean (leftSlots_eq S x) _ _ (leftReplay_heq S x)
  exact h.trans (heq_of_eq (WholeCutReplay.evaluateArrays_erase_of_grouped_zero
    rows repeats (CleanDecoderRate.path S) (leftSlots S x) (context S x).clean
    (leftTape S x) (left_grouped_zero S cube hcube x hx)))

theorem rightArrays_heq (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    HEq (CleanRightDecoder.arrays (context S x).clauses (context S x).designated
      (context S x).clean (context S x).visible (context S x).projected upper
      (CleanDecoderContext.lower (context S x)) (context S x).cut
      (CleanDecoderContext.lowerHeight upper d) (context S x).outside rows repeats
      (context S x).rightTape (rightOwn S x))
      (WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S) (rightSlots S x)
        (rightTape S x)) := by
  have h := evaluateArrays_heq rows repeats (CleanDecoderRate.path S)
    (CleanDecoderContext.rightSlots (context S x) (rightOwn S x)) (rightSlots S x)
    (context S x).clean (rightSlots_eq S x) _ _ (rightReplay_heq S x)
  exact h.trans (heq_of_eq (WholeCutReplay.evaluateArrays_erase_of_grouped_zero
    rows repeats (CleanDecoderRate.path S) (rightSlots S x) (context S x).clean
    (rightTape S x) (right_grouped_zero S cube hcube x hx)))

end
end PerfectCompleteness.CleanNativeReplay

end

end OAI
