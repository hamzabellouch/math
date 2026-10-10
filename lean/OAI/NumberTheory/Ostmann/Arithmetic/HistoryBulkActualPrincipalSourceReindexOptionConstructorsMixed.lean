import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionMeanProjection

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkActualPrincipalBlockFamily HistoryPairReferenceFlagExpectation
open HistoryBulkActualPrincipalSourceReindexCompensation HistoryGiantReferenceMean
open HistoryBulkFibreGiantApproximation
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (D : OuterData C p o) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
  (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
  (hp : ∀q∈outside,q.Prime)

theorem mixed_constructor_quotient
    (r : Witness C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      (fun i=>@HistoryBulkFibreGiantApproximation.plainMixedWeight d Bs BD Bz L k l E C outside (outerNonbulk C l p o) i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i)
    (hcell : ∀v,mixedWeight C.giantCenter C.giant v≠0 → 0 < mixedP C.giantCenter C.giant v ∧ 0 < mixedQ C.giantCenter C.giant v ∧
      |Real.log (mixedP C.giantCenter C.giant v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
      |Real.log (mixedQ C.giantCenter C.giant v:ℝ)-(C.giantCenter:ℝ)|≤1) :
    mixedWitnessPrincipal C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hp / blockJacobian C p D.blockDraw =
    (selectedBulkPrior C l).cmean ((⟨D,r⟩ : MatchedSelectedOuter C p o outside σ
      (fun i=>@HistoryBulkFibreGiantApproximation.plainMixedWeight d Bs BD Bz L k l E C outside (outerNonbulk C l p o) i.1.val) (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i).rawBTerm (l:=l)
      hcell hp false true) := by
  let R : MatchedSelectedOuter C p o outside σ
      (fun i=>@HistoryBulkFibreGiantApproximation.plainMixedWeight d Bs BD Bz L k l E C outside (outerNonbulk C l p o) i.1.val)
      (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i := ⟨D,r⟩
  have hq := @mixedWitnessPrincipal_div_blockJacobian d Bs BD Bz L k l E C p D.blockDraw D.valid
    outside σ (outerNonbulk C l p o) i r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hp
  have hf := @outer_constructor_mixed_frame d Bs BD Bz L k l E C p o D outside σ
    (fun i=>@HistoryBulkFibreGiantApproximation.plainMixedWeight d Bs BD Bz L k l E C outside (outerNonbulk C l p o) i.1.val)
    i hp r hcell
  have hr := rawBTerm_mean_eq_frameRawMean (l:=l) C outside σ R hcell hp true
  exact (quotient_frameRawMean C outside σ (outerNonbulk C l p o) true _ _ hq hf).trans hr.symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
