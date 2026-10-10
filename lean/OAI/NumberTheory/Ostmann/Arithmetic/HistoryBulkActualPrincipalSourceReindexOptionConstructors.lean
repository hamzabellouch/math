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

theorem prime_constructor_quotient
    (r : Witness C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      (fun _ _ _ _=>1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i)
    (hcell : ∀v,primeWeight C.giant v≠0 → 0<primeP C.giant v ∧ 0<primeQ C.giant v ∧
      |Real.log (primeP C.giant v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
      |Real.log (primeQ C.giant v:ℝ)-(C.giantCenter:ℝ)|≤1) :
    primeWitnessPrincipal C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hp / blockJacobian C p D.blockDraw =
    (selectedBulkPrior C l).cmean ((⟨D,r⟩ : MatchedSelectedOuter C p o outside σ
      (fun _ _ _ _=>1) (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i).rawBTerm (l:=l)
      hcell hp false false) :=
  (@quotient_frameRawMean d Bs BD Bz L k l E C outside σ (outerNonbulk C l p o)
    (primeWitnessFrame C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      (fun _ _ _ _=>1) r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hp)
    ((⟨D,r⟩ : MatchedSelectedOuter C p o outside σ (fun _ _ _ _=>1)
      (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i).frame (l:=l) hcell hp)
    false
    (primeWitnessPrincipal C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hp)
    (blockJacobian C p D.blockDraw)
    (@primeWitnessPrincipal_div_blockJacobian d Bs BD Bz L k l E C p D.blockDraw D.valid
      outside σ (outerNonbulk C l p o) i r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hp)
    (@outer_constructor_prime_frame d Bs BD Bz L k l E C p o D outside σ (fun _ _ _ _=>1)
      i hp r hcell)).trans
    (rawBTerm_mean_eq_frameRawMean (l:=l) C outside σ
      (⟨D,r⟩ : MatchedSelectedOuter C p o outside σ (fun _ _ _ _=>1)
        (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i) hcell hp false).symm

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
