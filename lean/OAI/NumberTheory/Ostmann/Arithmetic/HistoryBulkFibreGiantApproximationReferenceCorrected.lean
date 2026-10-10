import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReferenceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceSelection
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalRemainingRootMatchingActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReference
open Construction Conclusion HistoryGiantReferenceMean HistoryBulkSourceDisintegration
open HistoryBulkFibreOriginalReference HistoryBulkIndependentFibreReference
open HistoryGiantOriginalMeanFactorization (Current Choices history)
open HistoryDiagonalRemainingRootMatching HistoryPairBulkCoordinates HistoryPairBulkTransport
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
variable (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)

theorem corrected_reference_masses (r : Reference C outside a e s t c₁ c₂)
    (ha : 0 < (selectedNonbulkPrior C l).mass a) :
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass
      (fibreAssignment C a r.bulk) ≠ 0 ∧
    (assignmentPrior C.sources (SelectedTemplate k L l)).mass
      (rightAssignment C a e r.bulk r.compatible) ≠ 0 :=
  ⟨ne_of_gt (fibreAssignment_mass_pos C a r.bulk ha r.bulk_pos),r.right_mass⟩

theorem corrected_reference_data (r : Reference C outside a e s t c₁ c₂)
    (ha : 0 < (selectedNonbulkPrior C l).mass a) :
    IntegerReferenceData C (fibreAssignment C a r.bulk)
      (rightAssignment C a e r.bulk r.compatible)
      (mixedP C.giantCenter C.giant r.draw) (mixedQ C.giantCenter C.giant r.draw) := by
  have hm := corrected_reference_masses C outside a e s t c₁ c₂ r ha
  have hg := mixed_draw_cells C r.draw r.draw_pos
  exact ⟨hm.1,hm.2,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2⟩

def corrected_reference_matching (r : Reference C outside a e s t c₁ c₂)
    (he : PreservesRemainingBands _ e) (P Q : ℤ) :
    RootMatching (history C (fibreAssignment C a r.bulk) s P Q c₁)
      (history C (rightAssignment C a e r.bulk r.compatible) t P Q c₂) :=
  counterpartRootMatching C (frequencyBound Bs BD Bz k L)
    (fibreAssignment C a r.bulk) e he r.compatible s t P.toNat Q.toNat P.toNat Q.toNat c₁ c₂

def corrected_reference_draw_matching (r : Reference C outside a e s t c₁ c₂)
    (he : PreservesRemainingBands _ e) :
    RootMatching
      (history C (fibreAssignment C a r.bulk) s
        (mixedP C.giantCenter C.giant r.draw) (mixedQ C.giantCenter C.giant r.draw) c₁)
      (history C (rightAssignment C a e r.bulk r.compatible) t
        (mixedP C.giantCenter C.giant r.draw) (mixedQ C.giantCenter C.giant r.draw) c₂) :=
  corrected_reference_matching C outside a e s t c₁ c₂ r he _ _

end Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationReference

end

end OAI
