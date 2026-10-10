import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualGoodPrincipalReference
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOptionBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameFactories

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkSourceDisintegration HistoryBulkActualRootReferenceFamily HistoryBulkReferenceFrequencyFamily
open HistoryBulkFibreGiantErrorAverage HistoryBulkPrincipalSourceReindexWitness
open HistoryBulkActualPrincipalBlockFamily HistoryPairReferenceFlagExpectation
open HistoryBulkFibreGiantApproximation HistoryBulkActualPrincipalValueFrame
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
  (C : InitialSourceChoice d Bs BD Bz k L E)
  (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l))
  (o : OriginalOuter (fun _=>C.giant) C.sources (Template.initial (2*(bulkSize k L/2)) k) l p)
  (D : OuterData C p o) (outside : List ℕ)
  (σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
  (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)→SelectedBulkSample C l→ℤ→ℤ→ℂ)
  {α : Type} [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
  (i : RootFrequencyIndex (frequencyBound Bs BD Bz k L) l)
  (r : Witness C outside σ (outerNonbulk C l p o)
    (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid) J w P Q i)
  (hcell : ∀v,w v≠0 → 0<P v ∧ 0<Q v ∧
    |Real.log (P v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧ |Real.log (Q v:ℝ)-(C.giantCenter:ℝ)|≤1)
  (hp : ∀q∈outside,q.Prime)

theorem outer_constructor_frame :
    (MatchedSelectedOuter.frame (l:=l) (⟨D,r⟩ : MatchedSelectedOuter C p o outside σ J w P Q i)
      hcell hp) =
    witnessFrame C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      J w P Q i r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hcell hp := rfl

open HistoryGiantReferenceMean

theorem outer_constructor_prime_frame
    (r : Witness C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      J (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i)
    (hc : ∀v,(primeWeight C.giant) v≠0 → 0<(primeP C.giant) v ∧ 0<(primeQ C.giant) v ∧
      |Real.log ((primeP C.giant) v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
      |Real.log ((primeQ C.giant) v:ℝ)-(C.giantCenter:ℝ)|≤1) :
    (⟨D,r⟩ : MatchedSelectedOuter C p o outside σ J (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i).frame hc hp =
    primeWitnessFrame C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      J r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hp := rfl

theorem outer_constructor_mixed_frame
    (r : Witness C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      J (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i)
    (hc : ∀v,(mixedWeight C.giantCenter C.giant) v≠0 → 0<(mixedP C.giantCenter C.giant) v ∧ 0<(mixedQ C.giantCenter C.giant) v ∧
      |Real.log ((mixedP C.giantCenter C.giant) v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
      |Real.log ((mixedQ C.giantCenter C.giant) v:ℝ)-(C.giantCenter:ℝ)|≤1) :
    (⟨D,r⟩ : MatchedSelectedOuter C p o outside σ J (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i).frame hc hp =
    mixedWitnessFrame C outside σ (outerNonbulk C l p o)
      (leftDraws C p D.blockDraw D.valid) (rightDraws C p D.blockDraw D.valid)
      J r D.nonbulk_pos (D.left_mass i) (D.right_mass i) hp := rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexOption

end

end OAI
