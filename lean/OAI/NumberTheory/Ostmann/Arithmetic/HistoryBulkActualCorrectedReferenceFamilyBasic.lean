import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceFrameCorrected
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamily
open Construction Conclusion HistoryBulkSourceDisintegration
open HistoryBulkIndependentFibreReference HistoryBulkFibreGiantApproximation
open HistoryGiantOriginalMeanFactorization (Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
variable (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)

abbrev Witness := Reference C outside a e s t c₁ c₂

def selectWitness (ha : 0<(selectedNonbulkPrior C l).mass a) :
    Option (Witness C outside a e s t c₁ c₂) := by
  classical
  exact if hz : mixedFibreMean C outside a e s t c₁ c₂=0 then none else
    some (Classical.choice ((mixedFibreMean_eq_zero_or_reference C outside a e s t c₁ c₂ ha).resolve_left hz))

theorem selectWitness_none_iff (ha : 0<(selectedNonbulkPrior C l).mass a) :
    selectWitness C outside a e s t c₁ c₂ ha=none ↔
      mixedFibreMean C outside a e s t c₁ c₂=0 := by
  classical
  unfold selectWitness
  split_ifs <;> simp_all

theorem selectWitness_isSome_iff (ha : 0<(selectedNonbulkPrior C l).mass a) :
    (selectWitness C outside a e s t c₁ c₂ ha).isSome ↔
      mixedFibreMean C outside a e s t c₁ c₂≠0 := by
  classical
  unfold selectWitness
  split_ifs <;> simp_all

def witnessFrame (he : PreservesRemainingBands _ e)
    (ha : 0<(selectedNonbulkPrior C l).mass a)
    (hc₁ : choicesMass C.sources _ _ l c₁≠0)
    (hc₂ : choicesMass C.sources _ _ l c₂≠0)
    (hp : ∀q∈outside,q.Prime) (r : Witness C outside a e s t c₁ c₂) : Frame (l:=l) C outside :=
  correctedFrame C outside a e s t c₁ c₂ r ha he hc₁ hc₂ hp

end Ostmann.Arithmetic.HistoryBulkActualCorrectedReferenceFamily

end

end OAI
