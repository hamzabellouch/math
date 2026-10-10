import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipalAlignmentPointData

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryBulkActualRootReferenceFamily
open HistoryBulkActualPrincipalBlockFamily HistoryBulkSourceDisintegration
open HistoryBulkReferenceFrequencyFamily HistoryBulkSelectedUniversalOperator
open HistoryCompensationRepresentativePatterns HistoryPairKernelReplacement
open scoped BigOperators
attribute [local instance] Classical.propDecidable
local instance actualUniversalPrincipalPointKernelInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (D : OuterData C p o) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
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
  (i : RootPresent (referenceFamily C outside σ (outerNonbulk C l p o)
    (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
    J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos))

def alignmentSymbolicFamily :=
  symbolicPatternFamily C outside σ (outerNonbulk C l p o) p D.blockDraw D.valid
    J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos hcell

def alignmentMatchedOuter : MatchedSelectedOuter C p o outside σ J w P Q i.val :=
  ⟨D,presentWitness C outside σ (outerNonbulk C l p o)
    (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
    J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i⟩

def alignmentReferenceKernelProduct
    (j : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (r : SupportedReference C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) outside l
      (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
      j.1.val j.1.val j.2)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) (mixed : Bool) : ℝ :=
  ∏q : Block p,symbolicKernel mixed
    (blockLeftHistory C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) l p D.blockDraw D.valid r.left j.2.1)
    (blockRightHistory C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) l p D.blockDraw D.valid r.right j.2.2)
    r.left_supported r.right_supported
    ((decodedRepresentativeBlockEquiv C.sources (Template.initial (2*(bulkSize k L/2)) k)
      (frequencyBound Bs BD Bz k L) l p D.blockDraw D.valid r.left r.right
      j.2.1 j.2.2 r.left_matches r.right_matches).symm q) (b q).val

theorem symbolic_kernel_product_eq_reference
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) (mixed : Bool) :
    let F := alignmentSymbolicFamily C p o D outside σ J w P Q hactual hl houtside hw hpos hcell
    (∏q : Block p,symbolicKernel mixed (rootLeftHistory F.refs i) (rootRightHistory F.refs i)
      (rootLeftHistory_supported F.refs i) (rootRightHistory_supported F.refs i)
      (F.representative i q) (b q).val)=
    alignmentReferenceKernelProduct C p o D outside i.val (rootSelected F.refs i) b mixed := rfl

theorem matched_kernel_product_eq_reference
    (j : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
    (R : MatchedSelectedOuter C p o outside σ J w P Q j)
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) (mixed : Bool) :
    alignmentReferenceKernelProduct C p o R.data outside j R.witness.toReference b mixed=
    ∏q : Block p,symbolicKernel mixed (R.frame hcell hprime).left (R.frame hcell hprime).right
      (R.frame hcell hprime).left_supported (R.frame hcell hprime).right_supported
      (R.representative hcell hprime q) (b q).val := rfl

theorem symbolic_present_kernel_product_eq_matched
    (b : Block p → CommonSample C.sources
      (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) (mixed : Bool) :
    let F := alignmentSymbolicFamily C p o D outside σ J w P Q hactual hl houtside hw hpos hcell
    let R := alignmentMatchedOuter C p o D outside σ J w P Q hactual hl houtside hw hpos i
    (∏q : Block p,symbolicKernel mixed (rootLeftHistory F.refs i) (rootRightHistory F.refs i)
      (rootLeftHistory_supported F.refs i) (rootRightHistory_supported F.refs i)
      (F.representative i q) (b q).val)=
    ∏q : Block p,symbolicKernel mixed (R.frame hcell hprime).left (R.frame hcell hprime).right
      (R.frame hcell hprime).left_supported (R.frame hcell hprime).right_supported
      (R.representative hcell hprime q) (b q).val :=
  let R := alignmentMatchedOuter C p o D outside σ J w P Q hactual hl houtside hw hpos i
  let hleft := symbolic_kernel_product_eq_reference C p o D outside σ J w P Q hactual hl
    houtside hw hpos hcell i b mixed
  let hmid := congrArg (fun r=>alignmentReferenceKernelProduct C p o D outside i.val r b mixed)
    (rootSelected_eq_presentWitness C outside σ (outerNonbulk C l p o)
      (leftBlockDraws C p D.blockDraw D.valid) (rightBlockDraws C p D.blockDraw D.valid)
      J w P Q hactual hl D.nonbulk_pos D.left_mass D.right_mass houtside hw hpos i)
  let hright := matched_kernel_product_eq_reference C p o outside σ J w P Q hcell hprime i.val R b mixed
  hleft.trans (hmid.trans hright)

end Ostmann.Arithmetic.HistoryBulkActualUniversalPrincipal

end

end OAI
