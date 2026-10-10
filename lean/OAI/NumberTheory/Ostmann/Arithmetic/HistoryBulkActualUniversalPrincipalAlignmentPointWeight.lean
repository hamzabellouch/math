import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentPointKernel
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentPointWeightBasic
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
open HistoryBulkSelectedUniversalSymbolicFamily HistoryBulkFibreIntegralReplacementFrame
open HistoryBulkGoodPatternPrincipalFrame HistoryPairKernelReplacement
open HistoryCompensationRepresentativePatterns HistoryPairKernelReplacement
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance actualUniversalPrincipalPointWeightInternalDecidable (seed : List SourceSlot) (l : ℕ) :
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
  (hprime : ∀q∈outside,q.Prime)
  (i : RootPresent (referenceFamily C outside (Equiv.refl _) (outerNonbulk C l p o)
    (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
    J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos))

theorem symbolic_present_weight_eq_matched
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool) :
    let F := withDensity (symbolicPatternFamily C outside (Equiv.refl _) (outerNonbulk C l p o)
      p D.blockDraw D.valid J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass
      houtside hw hpos hcell) mixed
    let R : MatchedSelectedOuter C p o outside (Equiv.refl _) J w P Q i.val :=
      ⟨D,presentWitness C outside (Equiv.refl _) (outerNonbulk C l p o)
        (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
        J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i⟩
    (replacementReference F hprime i).weight b mixed =
      ((∏q : Block p,symbolicKernel mixed (R.frame hcell hprime).left
        (R.frame hcell hprime).right (R.frame hcell hprime).left_supported
        (R.frame hcell hprime).right_supported (R.representative hcell hprime q)
        (b q).val : ℝ) : ℂ) :=
  (replacementReference_weight_eq_kernels
    (withDensity (symbolicPatternFamily C outside (Equiv.refl _) (outerNonbulk C l p o)
      p D.blockDraw D.valid J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass
      houtside hw hpos hcell) mixed) hprime i b mixed).trans
    (congrArg Complex.ofReal
      (symbolic_present_kernel_product_eq_matched C p o D outside (Equiv.refl _)
        J w P Q hactual hl houtside hw hpos hcell hprime i b mixed))

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
