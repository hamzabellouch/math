import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyOuterData
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilySymbolic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkReferenceFrequencyFamily HistoryBulkSelectedUniversalOperator
open HistoryBulkSelectedUniversalSymbolicFamily
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance actualUniversalPrincipalPointFamilyDefsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (D : OuterData C p o) (outside : List ℕ)
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  {spectator : PrimeSource}
  (hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator)
  (hl : l≤k) (houtside : ∀q∈outside,∃v:spectator.Sample,(v:ℕ)=q)
  (hw : ∀v,0≤w v) (hpos : ∀v,w v≠0 → 0<P v ∧ 0<Q v)
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)

def alignmentDensityFamily (mixed : Bool) :
    HistoryBulkUniversalPatternAggregation.SymbolicPatternFamily C outside l p :=
  withDensity (symbolicPatternFamily C outside (Equiv.refl _) (outerNonbulk C l p o)
    p D.blockDraw D.valid J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass
    houtside hw hpos hcell) mixed

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
