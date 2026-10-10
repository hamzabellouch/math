import OAI.Computability.PerfectCompleteness.Decoding.UpperScalarCutReconstructionLemmas

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

private theorem scalarLaw_cast (repeats : Nat → Nat) (suffix : Path branch i k)
    (slots slots' : Slots branch i → Fin t → MixedSupport.Slot) (h : slots = slots') :
    (RecursiveSampler.law F2 repeats suffix (LeafDomain slots')).pushforward
        (Equiv.cast (congrArg
          (fun s : Slots branch i → Fin t → MixedSupport.Slot => ↥(H s)) h)).symm =
      RecursiveSampler.law F2 repeats suffix (LeafDomain slots) := by
  cases h
  change (RecursiveSampler.law F2 repeats suffix (LeafDomain slots)).pushforward id = _
  exact FiniteDistribution.pushforward_id _

theorem cutSpaceEquiv_scalarLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (RecursiveSampler.law F2 repeats suffix
        (r.family (LeafDomain (cutSlots p slots)))).pushforward
          (cutSpaceEquiv p r slots).symm =
      RecursiveSampler.law F2 repeats suffix (LeafDomain (cutSlots (p.append r) slots)) :=
  scalarLaw_cast repeats suffix (cutSlots (p.append r) slots)
    (cutSlots r (cutSlots p slots)) (cutSlots_append p r slots)

def freshExteriorLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (FreshExterior repeats p r slots) :=
  OriginalTerminalSplit.exteriorLaw F2 repeats r (LeafDomain (cutSlots p slots))

def freshValuesLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (FreshValues repeats p r slots) :=
  FiniteProduct.law (fun _ : TerminalCalls.TerminalIndex repeats r =>
    RecursiveSampler.law F2 repeats suffix (LeafDomain (cutSlots (p.append r) slots)))

theorem readFresh_law (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (RecursiveSampler.tapeLaw F2 repeats (r.append suffix) (LeafDomain (cutSlots p slots))).pushforward
      (readFresh repeats p r suffix slots) =
        (freshValuesLaw repeats p r suffix slots).product (freshExteriorLaw repeats p r slots) := by
  let A := LeafDomain (cutSlots p slots)
  let scalarTape := RecursiveSampler.tapeLaw F2 repeats suffix (r.family A)
  let value : RecursiveSampler.Tape F2 repeats suffix (r.family A) →
      H (cutSlots (p.append r) slots) := fun tape =>
    (cutSpaceEquiv p r slots).symm (RecursiveSampler.evaluate F2 repeats suffix (r.family A) tape)
  let callsValue : OriginalTerminalSplit.TerminalTape F2 repeats r suffix A →
      FreshValues repeats p r slots := fun tapes call => value (tapes call)
  have hvalue : scalarTape.pushforward value =
      RecursiveSampler.law F2 repeats suffix (LeafDomain (cutSlots (p.append r) slots)) := by
    calc
      _ = (RecursiveSampler.law F2 repeats suffix (r.family A)).pushforward
          (cutSpaceEquiv p r slots).symm :=
        (FiniteDistribution.pushforward_comp scalarTape
          (RecursiveSampler.evaluate F2 repeats suffix (r.family A))
          (cutSpaceEquiv p r slots).symm).symm
      _ = _ := cutSpaceEquiv_scalarLaw repeats p r suffix slots
  have hcalls : (OriginalTerminalSplit.terminalLaw F2 repeats r suffix A).pushforward
      callsValue = freshValuesLaw repeats p r suffix slots := by
    calc
      _ = FiniteProduct.law (fun _ : TerminalCalls.TerminalIndex repeats r =>
          scalarTape.pushforward value) :=
        FiniteProduct.pushforward_map
          (fun _ : TerminalCalls.TerminalIndex repeats r => scalarTape) (fun _ => value)
      _ = _ := congrArg (fun μ : FiniteDistribution (H (cutSlots (p.append r) slots)) =>
        FiniteProduct.law (fun _ : TerminalCalls.TerminalIndex repeats r => μ)) hvalue
  calc
    _ = ((RecursiveSampler.tapeLaw F2 repeats (r.append suffix) A).pushforward
        (OriginalTerminalSplit.splitTape F2 repeats r suffix A)).pushforward
          (fun z => (callsValue z.1, z.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((OriginalTerminalSplit.terminalLaw F2 repeats r suffix A).product
        (OriginalTerminalSplit.exteriorLaw F2 repeats r A)).pushforward
          (fun z => (callsValue z.1, z.2)) := by
      rw [OriginalTerminalSplit.split_tapeLaw]
    _ = ((OriginalTerminalSplit.terminalLaw F2 repeats r suffix A).pushforward
        callsValue).product
          ((OriginalTerminalSplit.exteriorLaw F2 repeats r A).pushforward id) :=
      FiniteDistribution.product_pushforward
        (OriginalTerminalSplit.terminalLaw F2 repeats r suffix A)
        (OriginalTerminalSplit.exteriorLaw F2 repeats r A) callsValue id
    _ = _ := by simp only [hcalls, FiniteDistribution.pushforward_id, freshExteriorLaw, A]

def exteriorLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutReconstruction.Exterior rows repeats p r slots) :=
  (OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).product
    (freshExteriorLaw repeats p r slots)

def valuesLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutCalls.Index rows repeats p r →
      H (cutSlots (p.append r) slots)) :=
  FiniteProduct.law (fun _ : UpperScalarCutCalls.Index rows repeats p r =>
    RecursiveSampler.law F2 repeats suffix (LeafDomain (cutSlots (p.append r) slots)))

def assembledEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((UpperScalarCutCalls.Index rows repeats p r → H (cutSlots (p.append r) slots)) ×
      OriginalWholeCut.ChildArrays rows (cutSlots (p.append r) slots)) ≃
        CutChildGrouping.Assembled (C := UpperScalarCutCalls.Index rows repeats p r)
          (cutSlots (p.append r) slots) rows := Equiv.refl _

def assembledLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (CutChildGrouping.Assembled
      (C := UpperScalarCutCalls.Index rows repeats p r) (cutSlots (p.append r) slots) rows) :=
  @FiniteDistribution.transport
    ((UpperScalarCutCalls.Index rows repeats p r → H (cutSlots (p.append r) slots)) ×
      OriginalWholeCut.ChildArrays rows (cutSlots (p.append r) slots))
    (CutChildGrouping.Assembled (C := UpperScalarCutCalls.Index rows repeats p r)
      (cutSlots (p.append r) slots) rows)
    (instFintypeProd _ _)
    (CutChildGrouping.assembledFintype (C := UpperScalarCutCalls.Index rows repeats p r)
      (cutSlots (p.append r) slots) rows)
    ((valuesLaw rows repeats p r (.step chosen q) slots).product
      (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q (cutSlots (p.append r) slots)))
    (assembledEquiv rows repeats p r slots)

def recordLaw (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    FiniteDistribution (UpperScalarCutReconstruction.Record rows repeats p r slots) :=
  (exteriorLaw rows repeats p r slots).product (assembledLaw rows repeats p r chosen q slots)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

theorem pack_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((OriginalWholeCutLaw.recordLaw rows repeats (p.append r) chosen q slots).product
      ((freshValuesLaw repeats p r (.step chosen q) slots).product
        (freshExteriorLaw repeats p r slots))).pushforward (packEquiv rows repeats p r slots) =
      recordLaw rows repeats p r chosen q slots := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  let scalar := RecursiveSampler.law F2 repeats (.step chosen q)
    (LeafDomain (cutSlots (p.append r) slots))
  change
    (OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).weight z.1.1 *
        ((∏ call : OriginalCutCalls.Index rows repeats (p.append r),
            scalar.weight (z.2.1 (.inl call))) *
          (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
            (cutSlots (p.append r) slots)).weight z.2.2) *
      ((∏ call : TerminalCalls.TerminalIndex repeats r,
          scalar.weight (z.2.1 (.inr call))) *
        (freshExteriorLaw repeats p r slots).weight z.1.2) =
      ((OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).weight z.1.1 *
        (freshExteriorLaw repeats p r slots).weight z.1.2) *
          ((∏ call : OriginalCutCalls.Index rows repeats (p.append r) ⊕
              TerminalCalls.TerminalIndex repeats r, scalar.weight (z.2.1 call)) *
            (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
              (cutSlots (p.append r) slots)).weight z.2.2)
  rw [Fintype.prod_sum_type]
  ring

theorem read_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots).product
      (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots)))).pushforward
          (read rows repeats p r chosen q slots) =
      recordLaw rows repeats p r chosen q slots := by
  calc
    _ = (((WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots).product
        (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)))).pushforward
            (fun tapes =>
              (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1,
                readFresh repeats p r (.step chosen q) slots tapes.2))).pushforward
                  (packEquiv rows repeats p r slots) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (((WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots).pushforward
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots)).product
          ((RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
            (LeafDomain (cutSlots p slots))).pushforward
              (readFresh repeats p r (.step chosen q) slots))).pushforward
                (packEquiv rows repeats p r slots) := by
      exact congrArg
        (fun μ : FiniteDistribution (OriginalWholeCut.Record rows repeats (p.append r) slots ×
            FreshRecord repeats p r slots) => μ.pushforward (packEquiv rows repeats p r slots))
        (FiniteDistribution.product_pushforward
          (WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots)
          (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
            (LeafDomain (cutSlots p slots)))
          (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots)
          (readFresh repeats p r (.step chosen q) slots))
    _ = _ := by
      rw [OriginalWholeCutLaw.readRecord_law, readFresh_law]
      exact pack_law rows repeats p r chosen q slots

theorem numberRecord_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (recordLaw rows repeats p r chosen q slots).pushforward (numberRecordEquiv rows repeats p r slots) =
      (exteriorLaw rows repeats p r slots).product
        ((OriginalChildBlocks.sourceLaw (UpperScalarCutCalls.count rows repeats n j (i + 1))
          rows repeats chosen q (cutSlots (p.append r) slots)).pushforward
            (OriginalChildBlocks.observed (UpperScalarCutCalls.count rows repeats n j (i + 1))
              rows repeats chosen q (cutSlots (p.append r) slots))) := by
  rw [OriginalWholeCutBridge.observed_product_law,
    ← FiniteDistribution.transport_eq_pushforward
      (recordLaw rows repeats p r chosen q slots) (numberRecordEquiv rows repeats p r slots)]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  let scalar := RecursiveSampler.law F2 repeats (.step chosen q)
    (LeafDomain (cutSlots (p.append r) slots))
  change (exteriorLaw rows repeats p r slots).weight z.1 *
      ((∏ call : UpperScalarCutCalls.Index rows repeats p r,
          scalar.weight (z.2.1 (UpperScalarCutCalls.numbering rows repeats p r call))) *
        (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
          (cutSlots (p.append r) slots)).weight z.2.2) =
    (exteriorLaw rows repeats p r slots).weight z.1 *
      ((∏ call : Fin (UpperScalarCutCalls.count rows repeats n j (i + 1)),
          scalar.weight (z.2.1 call)) *
        (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
          (cutSlots (p.append r) slots)).weight z.2.2)
  exact congrArg (fun w : ℝ => (exteriorLaw rows repeats p r slots).weight z.1 *
      (w * (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
        (cutSlots (p.append r) slots)).weight z.2.2))
    ((UpperScalarCutCalls.numbering rows repeats p r).prod_comp
      (fun call => scalar.weight (z.2.1 call)))

theorem numbered_read_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots).product
      (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots)))).pushforward
          (fun tapes => numberRecordEquiv rows repeats p r slots
            (read rows repeats p r chosen q slots tapes)) =
      (exteriorLaw rows repeats p r slots).product
        ((OriginalChildBlocks.sourceLaw (UpperScalarCutCalls.count rows repeats n j (i + 1))
          rows repeats chosen q (cutSlots (p.append r) slots)).pushforward
            (OriginalChildBlocks.observed (UpperScalarCutCalls.count rows repeats n j (i + 1))
              rows repeats chosen q (cutSlots (p.append r) slots))) := by
  rw [← FiniteDistribution.pushforward_comp, read_law, numberRecord_law]

theorem observe_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (recordLaw rows repeats p r chosen q slots).pushforward (observe rows repeats p r slots) =
      ((OriginalWholeCutLaw.recordLaw rows repeats (p.append r) chosen q slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots)).product
          (RecursiveSampler.law F2 repeats (r.append (.step chosen q))
            (LeafDomain (cutSlots p slots))) := by
  have hmap :
      (fun tapes => observe rows repeats p r slots (read rows repeats p r chosen q slots tapes)) =
        (fun tapes =>
          (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots
            (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1),
          RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
            (LeafDomain (cutSlots p slots)) tapes.2)) :=
    funext (fun tapes => observe_read rows repeats p r chosen q slots tapes)
  rw [← read_law rows repeats p r chosen q slots, FiniteDistribution.pushforward_comp, hmap]
  apply Eq.trans (FiniteDistribution.product_pushforward
    (A := OriginalWholeCutBridge.NumberedRecord rows repeats (p.append r) slots)
    (B := ↥(H (cutSlots p slots)))
    (WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots)
    (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
      (LeafDomain (cutSlots p slots)))
    (fun tape => OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots
      (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape))
    (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
      (LeafDomain (cutSlots p slots))))
  rw [← FiniteDistribution.pushforward_comp
      (WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots)
      (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots)
      (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots),
    OriginalWholeCutLaw.readRecord_law]
  rfl

theorem numberedObserve_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p r slots).product
      ((OriginalChildBlocks.sourceLaw (UpperScalarCutCalls.count rows repeats n j (i + 1))
        rows repeats chosen q (cutSlots (p.append r) slots)).pushforward
          (OriginalChildBlocks.observed (UpperScalarCutCalls.count rows repeats n j (i + 1))
            rows repeats chosen q (cutSlots (p.append r) slots)))).pushforward
              (numberedObserve rows repeats p r slots) =
      ((OriginalWholeCutLaw.recordLaw rows repeats (p.append r) chosen q slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots)).product
          (RecursiveSampler.law F2 repeats (r.append (.step chosen q))
            (LeafDomain (cutSlots p slots))) := by
  rw [← numberRecord_law rows repeats p r chosen q slots,
    FiniteDistribution.pushforward_comp]
  have hmap :
      (fun record => numberedObserve rows repeats p r slots
        (numberRecordEquiv rows repeats p r slots record)) = observe rows repeats p r slots :=
    funext (fun record => numberedObserve_numberRecord rows repeats p r slots record)
  rw [hmap]
  exact observe_law rows repeats p r chosen q slots

end
end PerfectCompleteness.UpperScalarCutLaw

end

end OAI
