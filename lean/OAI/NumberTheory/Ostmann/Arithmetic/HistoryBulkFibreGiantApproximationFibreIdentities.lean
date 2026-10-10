import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationMixedDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceFrameCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceFramePlain
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreOriginalReferenceWeighted
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryGiantReferenceMean HistoryGiantOriginalMeanFactorization
open HistoryDiagonalSmallOriginalMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {depth l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz depth L E) (outside : List ℕ)

def plainMixedWeight (a : SelectedNonbulkSample C l) (s : ℤ)
    (u : SelectedBulkSample C l) (P Q : ℤ) : ℂ :=
  (smallMultiplier C outside (fibreAssignment C a u) s P Q:ℂ)

def plainMixedFibreMean
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C) : ℂ :=
  weightedMixedFibreMean C outside σ a s t c e (plainMixedWeight C outside a s)

theorem plain_mixed_reference_mean
    (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l)))
    (a : SelectedNonbulkSample C l) (s t : ℤ) (c e : Choices (l:=l) C)
    (y₀ : SelectedBulkSample C l) (draw : MixedDraw C.giantCenter C.giant)
    (ha : 0<(selectedNonbulkPrior C l).mass a)
    (hy₀ : 0<(selectedBulkPrior C l).mass y₀)
    (hr : 0 < mixedWeight C.giantCenter C.giant draw)
    (hc : choicesMass C.sources _ _ l c≠0) (he : choicesMass C.sources _ _ l e≠0)
    (hs : FibreSupported C outside σ a s t c e y₀
      (mixedP C.giantCenter C.giant draw) (mixedQ C.giantCenter C.giant draw))
    (hp : ∀q∈outside,q.Prime) :
    let r := plainMixedFrame C outside σ a s t c e y₀ draw ha hy₀ hr hc he hs hp
    HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass
      (mixedWeight C.giantCenter C.giant) (fun u z=>
        weightedFibreReferenceTerm C outside σ a s t c e (plainMixedWeight C outside a s)
          depth y₀ (mixedP C.giantCenter C.giant draw) (mixedQ C.giantCenter C.giant draw)
          hs u (mixedP C.giantCenter C.giant z) (mixedQ C.giantCenter C.giant z)) =
      (selectedBulkPrior C l).cmean (fun u=>r.sourceMeanMixed σ
        (fibreAssignment C a u) (permuteAssignment C σ (fibreAssignment C a u))) := by
  dsimp only
  change HistoryBulkFibreReference.originalMean _ _ _ =
    (selectedBulkPrior C l).cmean (fun u=>mixedMean C.giantCenter C.giant
      (weightedFibreReferenceTerm C outside σ a s t c e (plainMixedWeight C outside a s)
        depth y₀ (mixedP C.giantCenter C.giant draw) (mixedQ C.giantCenter C.giant draw) hs u))
  simp only [HistoryBulkFibreReference.originalMean,FinitePrior.cmean,mixedMean_eq_weighted,
    Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

theorem corrected_mixed_reference_mean
    (a : SelectedNonbulkSample C l)
    (e : HistoryBulkIndependentFibreReference.RemainingPermutation (k:=depth) (L:=L) (l:=l))
    (he : PreservesRemainingBands _ e) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)
    (old : HistoryBulkIndependentFibreReference.Reference C outside a e s t c₁ c₂)
    (ha : 0<(selectedNonbulkPrior C l).mass a)
    (hc₁ : choicesMass C.sources _ _ l c₁≠0) (hc₂ : choicesMass C.sources _ _ l c₂≠0)
    (hp : ∀q∈outside,q.Prime) :
    let r := correctedFrame C outside a e s t c₁ c₂ old ha he hc₁ hc₂ hp
    HistoryBulkIndependentFibreReference.referenceMean C outside a e he s t c₁ c₂ depth old =
      (selectedBulkPrior C l).cmean (fun u=>r.sourceMeanCorrectedMixed
        (HistoryBulkIndependentFibreReference.bulkPermutation e he)
        (fibreAssignment C a u)
        (HistoryBulkIndependentFibreReference.rightAssignment C a e u
          (HistoryBulkIndependentFibreReference.reference_compatible_all C outside a e he s t c₁ c₂ old u))) := by
  rfl

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
