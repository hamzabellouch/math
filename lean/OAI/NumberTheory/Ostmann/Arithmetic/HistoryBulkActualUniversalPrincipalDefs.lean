import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterBackground
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterSupport
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyLaws
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationFibreIdentities

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairSourceLaws HistoryPairReferenceFlagExpectation HistoryBulkSourceDisintegration
open HistoryBulkUniversalPatternAggregation HistoryBulkActualPrincipalBlockFamily
open HistoryBulkActualRootReferenceFamily HistoryBulkFibreGiantApproximation
attribute [local instance] Classical.propDecidable
local instance universalPrincipalDefsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (hout : ∀q∈outside,q∈spectator.candidates)

def selectedFamily
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (o : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p)
    (mixed : Bool) : SymbolicPatternFamily C outside l p :=
  match outerData? C p o with
  | none => emptyFamily C outside p
  | some D =>
    if mixed then withDensity
      (mixedPatternFamily C outside (Equiv.refl _) (outerNonbulk C l p o)
        p D.blockDraw D.valid
        (fun i=>plainMixedWeight C outside (outerNonbulk C l p o) i.1.val)
        hactual hl D.nonbulk_pos D.left_mass D.right_mass
        (fun q hq=>⟨⟨q,hout q hq⟩,rfl⟩)) true
    else withDensity
      (primePatternFamily C outside (Equiv.refl _) (outerNonbulk C l p o)
        p D.blockDraw D.valid (fun _ _ _ _=>1)
        hactual hl D.nonbulk_pos D.left_mass D.right_mass
        (fun q hq=>⟨⟨q,hout q hq⟩,rfl⟩)) false

@[simp] theorem selectedFamily_permutation
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (o : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) (mixed : Bool) :
    (selectedFamily C outside hactual hl hout p o mixed).permutation=Equiv.refl _ := by
  unfold selectedFamily
  cases outerData? C p o <;> cases mixed <;> rfl

theorem selectedFamily_mask
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (o : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p) (mixed : Bool) :
    ∀i,(selectedFamily C outside hactual hl hout p o mixed).mask i=
      assignmentDensity ((selectedFamily C outside hactual hl hout p o mixed).data i).assignment mixed := by
  unfold selectedFamily
  cases hd : outerData? C p o with
  | none =>
    intro i
    exact False.elim (by simpa only [emptyFamily,Option.isSome_none,Bool.false_eq_true] using i.property)
  | some D =>
    cases mixed <;> intro i <;> rfl

def selectedValue
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (o : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p)
    (mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  (selectedFamily C outside hactual hl hout p o mixed).value
    (outerBlocks C l p o) mixed (bulkSize k L/2)
    (fun q hq=>spectator.prime q (hout q hq)) hV

def selectedAggregate (mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  ∑p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
    ∑o,(outerMass C l p o:ℂ)*(∏q : Block p,((outerBlocks C l p o q).val:ℂ))*
      (if Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q)) then
        selectedValue C outside hactual hl hout p o mixed hV else 0)

theorem selectedAggregate_eq_background (mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    selectedAggregate C outside hactual hl hout mixed hV =
      (backgroundPrior C l).cmean (fun bg=>
        patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
          (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
          (fun p b=>(selectedFamily C outside hactual hl hout p
            (restoreOuterBackground C l p bg b) mixed).value b mixed (bulkSize k L/2)
              (fun q hq=>spectator.prime q (hout q hq)) hV)) := by
  unfold selectedAggregate
  rw [outer_pattern_sum_eq_background_cmean C l]
  rfl

theorem selected_support_of_mass
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
    (o : OriginalOuter (fun _=>C.giant) C.sources
      (Template.initial (2*(bulkSize k L/2)) k) l p)
    (ho : outerMass C l p o≠0)
    (ht : Function.Injective (fun q=>(blockType p q,outerBlocks C l p o q))) :
    (outerData? C p o).isSome := outerData?_isSome_of_mass C p o ho ht

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
