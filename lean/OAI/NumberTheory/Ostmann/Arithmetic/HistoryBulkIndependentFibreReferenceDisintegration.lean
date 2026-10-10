import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceLaws

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreReference
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryGiantOriginalMeanFactorization (Current Choices)
open HistoryDiagonalSmallOriginalMean (smallAssignment)
open HistoryDiagonalCorrectedOriginalMean hiding originalMixedMean
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

theorem sourceMean_disintegration
    (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
    (e : RemainingPermutation (k:=k) (L:=L) (l:=l)) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C) :
    (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).cmean
      (fun x=>if hc : SmallCounterpartCompatible C.sources _ (smallAssignment C x) e then
        HistoryDiagonalCorrectedOriginalMean.originalMixedMean C outside x
          (counterpartCurrentAssignment C x e hc) s t c₁ c₂ else 0)=
    (selectedNonbulkPrior C l).cmean (fun a=>mixedFibreMean C outside a e s t c₁ c₂) := by
  rw [selected_source_cmean_disintegration C l]
  apply congrArg (fun f=>(selectedNonbulkPrior C l).cmean f)
  funext a
  apply congrArg (fun f=>(selectedBulkPrior C l).cmean f)
  funext u
  exact (mixedMean_term_eq C outside a e s t c₁ c₂ u).symm

end Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

end

end OAI
