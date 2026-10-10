import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReference

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryGiantOriginalMeanFactorization
open HistoryBulkFibreGiantApproximationReference HistoryPairBulkCoordinates
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
open HistoryBulkIndependentFibreReference HistoryDiagonalRemainingRootMatching
variable (a : SelectedNonbulkSample C l)
variable (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
variable (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)

def correctedFrame (r : Reference C outside a e s t c₁ c₂)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (he : PreservesRemainingBands _ e)
    (hc₁ : choicesMass C.sources _ _ l c₁ ≠ 0)
    (hc₂ : choicesMass C.sources _ _ l c₂ ≠ 0)
    (hp : ∀q∈outside,q.Prime) : Frame (l:=l) C outside :=
  let hd := corrected_reference_data C outside a e s t c₁ c₂ r ha
  { leftSource := fibreAssignment C a r.bulk
    rightSource := rightAssignment C a e r.bulk r.compatible
    s := s
    t := t
    P := mixedP C.giantCenter C.giant r.draw
    Q := mixedQ C.giantCenter C.giant r.draw
    leftChoices := c₁
    rightChoices := c₂
    left_mass := hd.left_mass
    right_mass := hd.right_mass
    left_choices_mass := hc₁
    right_choices_mass := hc₂
    plus_pos := hd.plus_pos
    minus_pos := hd.minus_pos
    plus_cell := hd.plus_cell
    minus_cell := hd.minus_cell
    left_supported := r.supported.1
    right_supported := r.supported.2
    matching := corrected_reference_draw_matching C outside a e s t c₁ c₂ r he
    outside_primes := hp }

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximation

end

end OAI
