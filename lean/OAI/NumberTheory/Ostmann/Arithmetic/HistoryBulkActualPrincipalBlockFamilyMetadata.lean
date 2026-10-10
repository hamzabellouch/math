import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamilyReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferencePlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceSourceBoundsBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily
open Construction CanonicalOccurrenceTransport Conclusion CompensationEqualityPatterns
open HistoryPairReferenceFlagExpectation HistoryCompensationRepresentativePatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryGiantOriginalMeanFactorization HistorySignedXiTransport
open HistoryPairPattern HistoryGiantReferenceMean HistoryPairBulkTransport
open HistoryGiantReferenceSourceBounds HistoryBulkFibreGiantApproximationReference
attribute [local instance] Classical.propDecidable
local instance actualPrincipalMetadataInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (b : BlockDraw p (CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)))
  (hb : ∀i,(expand p b i).val∈(C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l i)).candidates)
  (outside : List ℕ) (a : SelectedNonbulkSample C l)
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) → SelectedBulkSample C l → ℤ → ℤ → ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))
  (r : Witness C outside (Equiv.refl _) a (leftBlockDraws C p b hb) (rightBlockDraws C p b hb) J w P Q i)

theorem witnessBlockReference_rootAligned
    (j : Fin (Template.current (Template.initial (2*(bulkSize k L/2)) k) l).length) :
    coordinateSample _ (witnessBlockReference C p b hb outside a J w P Q i r).right.history
      (witnessBlockReference C p b hb outside a J w P Q i r).right.labels (.inr (.inl j))=
    coordinateSample _ (witnessBlockReference C p b hb outside a J w P Q i r).left.history
      (witnessBlockReference C p b hb outside a J w P Q i r).left.labels (.inr (.inl j)) := by
  have hleft := coordinateSample_root_assigned C.sources _ (frequencyBound Bs BD Bz k L) l
    (witnessRoot C p b hb outside a J w P Q i r)
    (blockLeftChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb i.2.1)
    (fibreAssignment C a r.bulk) rfl (Template.assignedSlots_matches _ _ _) j
  have hright := coordinateSample_root_assigned C.sources _ (frequencyBound Bs BD Bz k L) l
    (witnessRoot C p b hb outside a J w P Q i r)
    (blockRightChoices C.sources _ (frequencyBound Bs BD Bz k L) l p b hb i.2.2)
    (fibreAssignment C a r.bulk) rfl (Template.assignedSlots_matches _ _ _) j
  exact hright.trans hleft.symm

def witnessPrincipalData
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
      (leftChoices C (leftBlockDraws C p b hb) i)≠0)
    (he : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l
      (rightChoices C (rightBlockDraws C p b hb) i)≠0)
    (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
      |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
    (s : ℕ) (hlen : outside.length=2*s) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q)
    (independent : Bool) : PrincipalReferenceData C
      (witnessBlockReference C p b hb outside a J w P Q i r) := by
  have hm := (fibreAssignment_mass_pos C a r.bulk ha r.bulk_pos).ne'
  have hg := hcell r.giant r.giant_pos.ne'
  have hs := selected_reference_sourceBounds C (frequencyBound Bs BD Bz k L) l
    (fibreAssignment C a r.bulk) (fibreAssignment C a r.bulk) i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p b hb) i) (rightChoices C (rightBlockDraws C p b hb) i)
    (P r.giant) (Q r.giant) hm hm hc he hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  refine {
    rootMatching := ?_
    leftSource := hs.1
    rightSource := hs.2
    s := s
    outsideLength := hlen
    outsidePrime := hprime
    outsideFrequency := hV
    permutation := Equiv.refl _
    K := k
    independent := independent }
  have hmatch := plain_reference_matching C (Equiv.refl _) a i.1.val i.1.val
    (leftChoices C (leftBlockDraws C p b hb) i) (rightChoices C (rightBlockDraws C p b hb) i)
    r.bulk (P r.giant) (Q r.giant)
  simp only [permute_fibreAssignment,Equiv.refl_apply] at hmatch
  exact hmatch

end Ostmann.Arithmetic.HistoryBulkActualPrincipalBlockFamily

end

end OAI
