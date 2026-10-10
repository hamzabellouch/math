import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrameBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrame
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily HistoryBulkFibreGiantApproximationReference
open HistoryBulkFibreIntegralReplacementFrame HistoryBulkFibreSourceMean
open HistoryBulkSelectedPrincipalAmplitude HistoryBulkGiantCorrectedBounds
open HistoryPairGiantCoordinates HistoryBulkGoodPatternPrincipalFrame
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

open HistoryBulkFibreGiantErrorAverage
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
    (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
    (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
      SelectedBulkSample C l → ℤ → ℤ → ℂ)
    (i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l))

theorem witnessFrame_eq_primeWitnessFrame
    (r : Witness C outside σ a x y J (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hcell : ∀v,primeWeight C.giant v≠0 → 0<primeP C.giant v ∧ 0<primeQ C.giant v ∧
      |Real.log (primeP C.giant v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
      |Real.log (primeQ C.giant v:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hp : ∀q∈outside,q.Prime) :
    witnessFrame C outside σ a x y J (primeWeight C.giant) (primeP C.giant) (primeQ C.giant) i r ha hc he hcell hp =
      primeWitnessFrame C outside σ a x y J r ha hc he hp := rfl

theorem witnessFrame_eq_mixedWitnessFrame
    (r : Witness C outside σ a x y J (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hcell : ∀v,mixedWeight C.giantCenter C.giant v≠0 → 0 < mixedP C.giantCenter C.giant v ∧ 0 < mixedQ C.giantCenter C.giant v ∧
      |Real.log (mixedP C.giantCenter C.giant v:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
      |Real.log (mixedQ C.giantCenter C.giant v:ℝ)-(C.giantCenter:ℝ)|≤1)
    (hp : ∀q∈outside,q.Prime) :
    witnessFrame C outside σ a x y J (mixedWeight C.giantCenter C.giant) (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i r ha hc he hcell hp =
      mixedWitnessFrame C outside σ a x y J r ha hc he hp := rfl

end Ostmann.Arithmetic.HistoryBulkActualPrincipalValueFrame

end

end OAI
