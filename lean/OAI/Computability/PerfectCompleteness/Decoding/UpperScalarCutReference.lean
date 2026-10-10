import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutLaw
import OAI.Computability.PerfectCompleteness.Sampling.NumberedUniformCut

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutReference

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

private theorem uniform_equiv {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (e : A ≃ B) :
    (FiniteDistribution.uniform A).pushforward e = FiniteDistribution.uniform B := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport e

variable {branch : Nat → Nat} {n j i t : Nat}

def freshReferenceLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (FreshRecord repeats p r slots) :=
  (FiniteDistribution.uniform (FreshValues repeats p r slots)).product
    (UpperScalarCutLaw.freshExteriorLaw repeats p r slots)

theorem freshReferenceLaw_uniform (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    freshReferenceLaw repeats p r slots =
      FiniteDistribution.uniform (FreshRecord repeats p r slots) := by
  unfold freshReferenceLaw UpperScalarCutLaw.freshExteriorLaw
  rw [OriginalTerminalSplit.exteriorLaw_uniform, WholeCutSampler.uniform_product]

def freshStoppedTapeEquiv (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FreshRecord repeats p r slots ≃
      RecursiveSampler.Tape F2 repeats r (LeafDomain (cutSlots p slots)) :=
  (Equiv.prodCongr
    (Equiv.arrowCongr (Equiv.refl (TerminalCalls.TerminalIndex repeats r))
      (cutSpaceEquiv p r slots))
    (Equiv.refl (FreshExterior repeats p r slots))).trans
      (OriginalScalarReconstruction.prefixSplit F2 repeats r
        (LeafDomain (cutSlots p slots))).symm

theorem freshStoppedTape_law (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (freshReferenceLaw repeats p r slots).pushforward
        (freshStoppedTapeEquiv repeats p r slots) =
      RecursiveSampler.tapeLaw F2 repeats r (LeafDomain (cutSlots p slots)) := by
  rw [freshReferenceLaw_uniform, RecursiveSampler.tapeLaw_eq_uniform]
  exact uniform_equiv (freshStoppedTapeEquiv repeats p r slots)

theorem reconstructFresh_referenceLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (freshReferenceLaw repeats p r slots).pushforward (reconstructFresh repeats p r slots) =
      RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p slots)) := by
  change (freshReferenceLaw repeats p r slots).pushforward
      (fun record => RecursiveSampler.evaluate F2 repeats r (LeafDomain (cutSlots p slots))
        (freshStoppedTapeEquiv repeats p r slots record)) =
    (RecursiveSampler.tapeLaw F2 repeats r (LeafDomain (cutSlots p slots))).pushforward
      (RecursiveSampler.evaluate F2 repeats r (LeafDomain (cutSlots p slots)))
  rw [← FiniteDistribution.pushforward_comp, freshStoppedTape_law]

theorem exteriorLaw_uniform (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    UpperScalarCutLaw.exteriorLaw rows repeats p r slots =
      FiniteDistribution.uniform (UpperScalarCutReconstruction.Exterior rows repeats p r slots) := by
  unfold UpperScalarCutLaw.exteriorLaw UpperScalarCutLaw.freshExteriorLaw
    OriginalWholeCutTape.exteriorLaw
  rw [OriginalTerminalSplit.exteriorLaw_uniform, WholeCutSampler.uniform_product]

def referenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutReconstruction.Record rows repeats p r slots) :=
  (UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    (FiniteDistribution.uniform (CutChildGrouping.Assembled
      (C := UpperScalarCutCalls.Index rows repeats p r) (cutSlots (p.append r) slots) rows))

theorem referenceLaw_uniform (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    referenceLaw rows repeats p r slots =
      FiniteDistribution.uniform (UpperScalarCutReconstruction.Record rows repeats p r slots) := by
  rw [referenceLaw, exteriorLaw_uniform, WholeCutSampler.uniform_product]

def numberedReferenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots) :=
  (UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    (FiniteDistribution.uniform (CutChildGrouping.Assembled
      (C := Fin (UpperScalarCutCalls.count rows repeats n j (i + 1)))
      (cutSlots (p.append r) slots) rows))

theorem numberedReferenceLaw_uniform (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    numberedReferenceLaw rows repeats p r slots =
      FiniteDistribution.uniform (UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots) := by
  rw [numberedReferenceLaw, exteriorLaw_uniform, WholeCutSampler.uniform_product]

theorem numberRecord_referenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (referenceLaw rows repeats p r slots).pushforward (numberRecordEquiv rows repeats p r slots) =
      numberedReferenceLaw rows repeats p r slots := by
  rw [referenceLaw_uniform, numberedReferenceLaw_uniform]
  exact uniform_equiv (numberRecordEquiv rows repeats p r slots)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

theorem pack_referenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((OriginalUniformCut.referenceLaw rows repeats (p.append r) slots).product
        (freshReferenceLaw repeats p r slots)).pushforward (packEquiv rows repeats p r slots) =
      referenceLaw rows repeats p r slots := by
  rw [OriginalUniformCut.referenceLaw_uniform, freshReferenceLaw_uniform,
    WholeCutSampler.uniform_product, referenceLaw_uniform]
  exact uniform_equiv (packEquiv rows repeats p r slots)

private theorem reference_pair_map {A B : Type*} [Fintype A] [Fintype B]
    (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (f : OriginalWholeCut.Record rows repeats (p.append r) slots → A)
    (g : FreshRecord repeats p r slots → B) :
    (referenceLaw rows repeats p r slots).pushforward
        (fun record => (f (oldRecord rows repeats p r slots record),
          g (freshRecord rows repeats p r slots record))) =
      ((OriginalUniformCut.referenceLaw rows repeats (p.append r) slots).pushforward f).product
        ((freshReferenceLaw repeats p r slots).pushforward g) := by
  rw [← pack_referenceLaw rows repeats p r slots, FiniteDistribution.pushforward_comp]
  change ((OriginalUniformCut.referenceLaw rows repeats (p.append r) slots).product
    (freshReferenceLaw repeats p r slots)).pushforward (fun z => (f z.1, g z.2)) = _
  exact FiniteDistribution.product_pushforward _ _ f g

theorem observe_referenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (referenceLaw rows repeats p r slots).pushforward (observe rows repeats p r slots) =
      ((OriginalUniformCut.referenceLaw rows repeats (p.append r) slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots)).product
          (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p slots))) := by
  change (referenceLaw rows repeats p r slots).pushforward
    (fun record =>
      (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots
        (oldRecord rows repeats p r slots record),
      reconstructFresh repeats p r slots (freshRecord rows repeats p r slots record))) = _
  rw [reference_pair_map, reconstructFresh_referenceLaw]

theorem reconstruct_referenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (referenceLaw rows repeats p r slots).pushforward
        (UpperScalarCutReconstruction.reconstruct rows repeats p r slots) =
      (WholeArraySampler.law rows repeats (p.append r) slots).product
        (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p slots))) := by
  change (referenceLaw rows repeats p r slots).pushforward
    (fun record =>
      (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots
        (oldRecord rows repeats p r slots record),
      reconstructFresh repeats p r slots (freshRecord rows repeats p r slots record))) = _
  rw [reference_pair_map, OriginalUniformCut.reconstruct_referenceLaw,
    reconstructFresh_referenceLaw]

theorem numberedObserve_referenceLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (numberedReferenceLaw rows repeats p r slots).pushforward
        (numberedObserve rows repeats p r slots) =
      ((OriginalUniformCut.referenceLaw rows repeats (p.append r) slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots)).product
          (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p slots))) := by
  rw [← numberRecord_referenceLaw rows repeats p r slots, FiniteDistribution.pushforward_comp]
  have hmap : (fun record : UpperScalarCutReconstruction.Record rows repeats p r slots =>
      numberedObserve rows repeats p r slots (numberRecordEquiv rows repeats p r slots record)) =
      observe rows repeats p r slots :=
    funext (numberedObserve_numberRecord rows repeats p r slots)
  rw [hmap]
  exact observe_referenceLaw rows repeats p r slots

end
end PerfectCompleteness.UpperScalarCutReference

end

end OAI
