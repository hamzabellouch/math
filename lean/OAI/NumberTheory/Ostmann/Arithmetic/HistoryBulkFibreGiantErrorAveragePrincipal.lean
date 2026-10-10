import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageWitness

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion HistoryBulkSourceDisintegration HistoryGiantReferenceMean
open HistoryBulkFibreOriginalReference HistoryBulkFibreGiantApproximation
open HistoryBulkActualRootReferenceFamily HistoryBulkReferencePeriodicMeanSource
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
variable (a : SelectedNonbulkSample C l) (x y : Draws C (l:=l))
variable {i : Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l)}

def primeWitnessPrincipal
    (r : Witness C outside σ a x y (fun _ _ _ _ => 1) (primeWeight C.giant)
      (primeP C.giant) (primeQ C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) : ℂ :=
  let f := primeWitnessFrame C outside σ a x y (fun _ _ _ _ => 1) r ha hc he hp
  oldCompensation f.left f.right * (selectedBulkPrior C l).cmean (fun u =>
    staticPairMask (f.newLeft (fibreAssignment C a u))
      (f.newRight (permuteAssignment C σ (fibreAssignment C a u))) outside *
      f.principal σ (fibreAssignment C a u) (permuteAssignment C σ (fibreAssignment C a u)))

def mixedWitnessPrincipal
    (r : Witness C outside σ a x y
      (fun i => plainMixedWeight C outside a i.1.val)
      (mixedWeight C.giantCenter C.giant)
      (mixedP C.giantCenter C.giant) (mixedQ C.giantCenter C.giant) i)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc : choicesMass C.sources _ _ l (leftChoices C x i) ≠ 0)
    (he : choicesMass C.sources _ _ l (rightChoices C y i) ≠ 0)
    (hp : ∀q∈outside,q.Prime) : ℂ :=
  let f := mixedWitnessFrame C outside σ a x y
    (fun i => plainMixedWeight C outside a i.1.val) r ha hc he hp
  oldCompensation f.left f.right * (selectedBulkPrior C l).cmean (fun u =>
    staticPairMask (f.newLeft (fibreAssignment C a u))
      (f.newRight (permuteAssignment C σ (fibreAssignment C a u))) outside *
      f.principalMixed σ (fibreAssignment C a u) (permuteAssignment C σ (fibreAssignment C a u)))

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
