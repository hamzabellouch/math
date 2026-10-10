import OAI.Computability.PerfectCompleteness.Decoding.UpperCutTriangle
import OAI.Computability.PerfectCompleteness.Foundations.ProjectedCallRestriction

namespace OAI

section

namespace PerfectCompleteness.UpperCutOldRecord

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

private theorem product_swap {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward (Equiv.prodComm A B) = ν.product μ := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  exact mul_comm _ _

private theorem product_fst {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward Prod.fst = μ := by
  calc
    _ = ((μ.product ν).pushforward (Equiv.prodComm A B)).pushforward Prod.snd :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by rw [product_swap, FiniteDistribution.product_pushforward_snd]

variable {branch : Nat → Nat} {n j i t : Nat}

local instance backgroundFintype (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (HierarchicalAgreementMean.Background (rows := rows) slots (upperNode p)) :=
  Fintype.ofFinite _

local instance rowSpaceFintype (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _

abbrev OldRecord (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :=
  HierarchicalAgreementMean.Background (rows := rows) slots (upperNode p) ×
    HierarchicalAgreementMean.Matrix (rows := rows) slots (upperNode p)

def oldView (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : HierarchicalAgreementMean.PairRecord (rows := rows) slots (upperNode p)) :
    OldRecord rows p slots := (record.1, record.2.1)

def arrayView (rows : Nat → Nat) (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    OldRecord rows p slots :=
  (HierarchicalMatrixTable.backgroundOf slots (upperNode p) arrays,
    NodeEmbedding.matrix arrays (upperNode p))

def oldCall (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) :
    Fin (OriginalCutCalls.count rows repeats n (i + 1)) →
      Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) :=
  fun call => UpperScalarCutCalls.numbering rows repeats p r
    (.inl ((OriginalWholeCut.callNumbering rows repeats (p.append r)).symm call))

theorem oldCall_injective (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) :
    Function.Injective (oldCall rows repeats p r) := by
  intro a b h
  apply (OriginalWholeCut.callNumbering rows repeats (p.append r)).symm.injective
  exact Sum.inl.inj ((UpperScalarCutCalls.numbering rows repeats p r).injective h)

def restrictedRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots) :
    OriginalWholeCutBridge.NumberedRecord rows repeats (p.append r) slots :=
  (record.1.1, ProjectedCallRestriction.assembledRestrict rows
    (cutSlots (p.append r) slots) (oldCall rows repeats p r) record.2)

theorem number_oldRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots) :
    OriginalWholeCutBridge.numberRecord rows repeats (p.append r) slots
      (UpperScalarCutReconstruction.oldRecord rows repeats p r slots
        ((UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots).symm record)) =
      restrictedRecord rows repeats p r slots record := by
  rfl

theorem oldView_numberedPairRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (j + 1)) ×
      UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots) :
    oldView rows p slots (UpperScalarCutBucket.numberedPairRecord rows repeats p r slots sample) =
      arrayView rows p slots (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots
        (restrictedRecord rows repeats p r slots sample.2)) := by
  change arrayView rows p slots
    (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots
      (UpperScalarCutReconstruction.oldRecord rows repeats p r slots
        ((UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots).symm sample.2))) = _
  apply congrArg (arrayView rows p slots)
  exact (OriginalWholeCutBridge.reconstruct_numberRecord rows repeats (p.append r) slots _).symm.trans
    (congrArg (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots)
      (number_oldRecord rows repeats p r slots sample.2))

variable {Z : Fin (branch i) → Type*} [∀ child, Fintype (Z child)]

def arrayLaw (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (child : Fin (branch i)) → Z child → Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ child z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append r) slots) child s a) (projected child z s a))
    (choiceLaw : (child : Fin (branch i)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) : FiniteDistribution (Arrays slots rows) :=
  ((OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).product
    (ProjectedPrefixComparison.assembledLaw (OriginalCutCalls.count rows repeats n (i + 1))
      rows (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ')).pushforward
        (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots)

theorem restrictedRecord_law (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (child : Fin (branch i)) → Z child → Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ child z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append r) slots) child s a) (projected child z s a))
    (choiceLaw : (child : Fin (branch i)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ((UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
      (ProjectedPrefixComparison.assembledLaw (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1))
        rows (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ')).pushforward
          (restrictedRecord rows repeats p r slots) =
      (OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).product
        (ProjectedPrefixComparison.assembledLaw (OriginalCutCalls.count rows repeats n (i + 1))
          rows (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ') := by
  have h := FiniteDistribution.product_pushforward
    (UpperScalarCutLaw.exteriorLaw rows repeats p r slots)
    (ProjectedPrefixComparison.assembledLaw (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1))
      rows (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ')
    Prod.fst (ProjectedCallRestriction.assembledRestrict rows (cutSlots (p.append r) slots)
      (oldCall rows repeats p r))
  rw [UpperScalarCutLaw.exteriorLaw, product_fst,
    ProjectedCallRestriction.assembled_restrict_law rows (cutSlots (p.append r) slots)
      projected projection choiceLaw β hβ hβ' (oldCall rows repeats p r)
      (oldCall_injective rows repeats p r)] at h
  exact h

theorem pairLaw_oldView (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (projected : (child : Fin (branch i)) → Z child → Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ child z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append r) slots) child s a) (projected child z s a))
    (choiceLaw : (child : Fin (branch i)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      (ProjectedPrefixComparison.assembledLaw (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1))
        rows (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ')).pushforward
          (oldView rows p slots) =
      (arrayLaw rows repeats p r slots projected projection choiceLaw β hβ hβ').pushforward
        (arrayView rows p slots) := by
  let P := (UpperScalarCutLaw.exteriorLaw rows repeats p r slots).product
    (ProjectedPrefixComparison.assembledLaw (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1))
      rows (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ')
  calc
    _ = (directions.product P).pushforward (fun sample =>
        arrayView rows p slots (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots
          (restrictedRecord rows repeats p r slots sample.2))) := by
      rw [UpperScalarPairComparison.pairLaw, FiniteDistribution.pushforward_comp]
      exact congrArg (FiniteDistribution.pushforward (directions.product P))
        (funext (oldView_numberedPairRecord rows repeats p r slots))
    _ = ((directions.product P).pushforward Prod.snd).pushforward (fun record =>
        arrayView rows p slots (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots
          (restrictedRecord rows repeats p r slots record))) :=
      (FiniteDistribution.pushforward_comp (directions.product P)
        (Prod.snd : BucketSampler.Direction (rows (j + 1)) ×
          UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots →
            UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots)
        (fun record : UpperScalarCutReconstruction.NumberedRecord rows repeats p r slots =>
          arrayView rows p slots (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots
            (restrictedRecord rows repeats p r slots record)))).symm
    _ = P.pushforward (fun record => arrayView rows p slots
        (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots
          (restrictedRecord rows repeats p r slots record))) := by
      rw [FiniteDistribution.product_pushforward_snd]
    _ = (P.pushforward (restrictedRecord rows repeats p r slots)).pushforward (fun record =>
        arrayView rows p slots (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots record)) :=
      (FiniteDistribution.pushforward_comp P (restrictedRecord rows repeats p r slots)
        (fun record : OriginalWholeCutBridge.NumberedRecord rows repeats (p.append r) slots =>
          arrayView rows p slots
            (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots record))).symm
    _ = _ := by
      dsimp only [P]
      rw [restrictedRecord_law rows repeats p r slots projected projection choiceLaw β hβ hβ']
      exact (FiniteDistribution.pushforward_comp
        ((OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).product
          (ProjectedPrefixComparison.assembledLaw (OriginalCutCalls.count rows repeats n (i + 1))
            rows (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ'))
        (OriginalWholeCutBridge.reconstruct rows repeats (p.append r) slots)
        (arrayView rows p slots)).symm

variable {Y : UpperCutTriangle.Prefix branch j i → Fin (branch i) → Type*}
  [∀ lowerPref child, Fintype (Y lowerPref child)]

def modifiedArrayLaw (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (hcut : i + 1 ≤ j + 1) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < j + 1, 0 < branch k)
    (projected : (lowerPref : UpperCutTriangle.Prefix branch j i) →
      (child : Fin (branch i)) → Y lowerPref child → Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ lowerPref child z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append (GeometricCutSplit.prefixPath hcut lowerPref)) slots) child s a)
      (projected lowerPref child z s a))
    (choiceLaw : (lowerPref : UpperCutTriangle.Prefix branch j i) →
      (child : Fin (branch i)) → FiniteDistribution (Y lowerPref child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) : FiniteDistribution (Arrays slots rows) :=
  (GeometricCutSplit.prefixLaw hcut hbranch).mixture (fun lowerPref =>
    arrayLaw rows repeats p (GeometricCutSplit.prefixPath hcut lowerPref) slots
      (projected lowerPref) (projection lowerPref) (choiceLaw lowerPref) β hβ hβ')

theorem modifiedPair_oldView (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (hcut : i + 1 ≤ j + 1) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : 0 < rows (j + 1))
    (projected : (lowerPref : UpperCutTriangle.Prefix branch j i) →
      (child : Fin (branch i)) → Y lowerPref child → Slots branch i → Fin t → MixedSupport.Slot)
    (projection : ∀ lowerPref child z s a, MixedSupport.Projection
      (childSlots (cutSlots (p.append (GeometricCutSplit.prefixPath hcut lowerPref)) slots) child s a)
      (projected lowerPref child z s a))
    (choiceLaw : (lowerPref : UpperCutTriangle.Prefix branch j i) →
      (child : Fin (branch i)) → FiniteDistribution (Y lowerPref child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (UpperCutTriangle.modifiedPairLaw rows repeats p hcut slots hbranch hrows
      projected projection choiceLaw β hβ hβ').pushforward (oldView rows p slots) =
    (modifiedArrayLaw rows repeats p hcut slots hbranch projected projection choiceLaw β hβ hβ').pushforward (arrayView rows p slots) := by
  simp only [UpperCutTriangle.modifiedPairLaw, modifiedArrayLaw,
    FiniteDistribution.pushforward_mixture]
  apply congrArg ((GeometricCutSplit.prefixLaw hcut hbranch).mixture)
  funext lowerPref
  exact pairLaw_oldView rows repeats p (GeometricCutSplit.prefixPath hcut lowerPref) slots
    (projected lowerPref) (projection lowerPref) (choiceLaw lowerPref) β hβ hβ'
    (OriginalCutPairLaw.directionsLaw rows j hrows)

end
end PerfectCompleteness.UpperCutOldRecord

end

end OAI
