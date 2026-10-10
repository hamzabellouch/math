import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationFibreIdentities
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageCompensation

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
variable (J : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
  SelectedBulkSample C l → ℤ → ℤ → ℂ)
variable {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

def primeWitnessFrame
    (r : Witness C outside σ a x y J (primeWeight C.giant)
      (primeP C.giant) (primeQ C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) : Frame (l:=l) C outside :=
  plainPrimeFrame C outside σ a i.1.val i.1.val (leftChoices C x i) (rightChoices C y i)
    r.bulk r.giant ha r.bulk_pos r.giant_pos hc he r.supported hp

def mixedWitnessFrame
    (r : Witness C outside σ a x y J (mixedWeight C.giantCenter C.giant)
      (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) : Frame (l:=l) C outside :=
  plainMixedFrame C outside σ a i.1.val i.1.val (leftChoices C x i) (rightChoices C y i)
    r.bulk r.giant ha r.bulk_pos r.giant_pos hc he r.supported hp

theorem primeWitnessMean_eq_source
    (r : Witness C outside σ a x y (fun _ _ _ _ => 1) (primeWeight C.giant)
      (primeP C.giant) (primeQ C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) :
    let f := primeWitnessFrame C outside σ a x y (fun _ _ _ _ => 1) r ha hc he hp
    wholeMean C outside σ a x y (fun _ _ _ _ => 1) (primeWeight C.giant)
      (primeP C.giant) (primeQ C.giant) i =
      (selectedBulkPrior C l).cmean (fun u =>
        f.sourceMean σ (fibreAssignment C a u)
          (permuteAssignment C σ (fibreAssignment C a u))) := by
  dsimp only
  rw [r.mean_eq]
  change HistoryBulkFibreReference.originalMean _ _ _ =
    (selectedBulkPrior C l).cmean (fun u => primeMean C.giant
      (weightedFibreReferenceTerm C outside σ a i.1.val i.1.val
        (leftChoices C x i) (rightChoices C y i) (fun _ _ _ => 1)
        k r.bulk (primeP C.giant r.giant) (primeQ C.giant r.giant) r.supported u))
  simp only [HistoryBulkFibreReference.originalMean,FinitePrior.cmean,primeMean_eq_weighted,
    Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

theorem mixedWitnessMean_eq_source
    (r : Witness C outside σ a x y
      (fun i => plainMixedWeight C outside a i.1.val)
      (mixedWeight C.giantCenter C.giant)
      (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) :
    let f := mixedWitnessFrame C outside σ a x y
      (fun i => plainMixedWeight C outside a i.1.val) r ha hc he hp
    wholeMean C outside σ a x y (fun i => plainMixedWeight C outside a i.1.val)
      (mixedWeight C.giantCenter C.giant)
      (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i =
      (selectedBulkPrior C l).cmean (fun u =>
        f.sourceMeanMixed σ (fibreAssignment C a u)
          (permuteAssignment C σ (fibreAssignment C a u))) := by
  dsimp only
  exact r.mean_eq.trans (plain_mixed_reference_mean C outside σ a i.1.val i.1.val
    (leftChoices C x i) (rightChoices C y i) r.bulk r.giant ha r.bulk_pos r.giant_pos
    hc he r.supported hp)

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
