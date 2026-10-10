import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentPointFrame
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentPointRepresentative
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkSelectedUniversalOperator HistoryBulkFibreIntegralReplacementFrame
open HistoryBulkGoodPatternPrincipalFrame HistoryPairKernelReplacement
open HistoryBulkReferenceFrequencyFamily HistoryCompensationRepresentativePatterns
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E}
  {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
  {o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p}
  {outside : List ℕ}
  {J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
    SelectedBulkSample C l → ℤ → ℤ → ℂ}
  {α : Type} [Fintype α] {w : α→ℝ} {P Q : α→ℤ}
  {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}
  (R : MatchedSelectedOuter C p o outside (Equiv.refl _) J w P Q i)
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hprime : ∀q∈outside,q.Prime)

theorem matched_principal_term_eq_data
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) :
    let a := R.witness.toActualData C outside (Equiv.refl _) (outerNonbulk C l p o)
      (leftBlockDraws C p R.data.blockDraw R.data.valid)
      (rightBlockDraws C p R.data.blockDraw R.data.valid) J w P Q
      R.data.nonbulk_pos (R.data.left_mass i) (R.data.right_mass i) hcell
    let K : ℂ := ((∏q : Block p, symbolicKernel mixed
      (R.frame hcell hprime).left (R.frame hcell hprime).right
      (R.frame hcell hprime).left_supported (R.frame hcell hprime).right_supported
      (R.representative hcell hprime q) (b q).val : ℝ) : ℂ)
    rootDensity (R.frame hcell hprime) mixed * K *
        principalOperator (R.frame hcell hprime) false mixed (Equiv.refl _) hV =
      (assignmentDensity a.assignment mixed : ℂ) * K *
        actualNestedIntegral C mixed (bulkSize k L/2) a *
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) (Equiv.refl _) hprime hV
          R.witness.toReference := by
  dsimp only
  let a := R.witness.toActualData C outside (Equiv.refl _) (outerNonbulk C l p o)
      (leftBlockDraws C p R.data.blockDraw R.data.valid)
      (rightBlockDraws C p R.data.blockDraw R.data.valid) J w P Q
      R.data.nonbulk_pos (R.data.left_mass i) (R.data.right_mass i) hcell
  have ho : principalOperator (R.frame hcell hprime) false mixed (Equiv.refl _) hV =
      actualNestedIntegral C mixed (bulkSize k L/2) a *
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) (Equiv.refl _) hprime hV
          R.witness.toReference := frameOfData_operator a hprime mixed hV
  have hd : rootDensity (R.frame hcell hprime) mixed =
      (assignmentDensity a.assignment mixed : ℂ) := (frameOfData_density a hprime mixed).symm
  rw [ho,hd]
  ring

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
