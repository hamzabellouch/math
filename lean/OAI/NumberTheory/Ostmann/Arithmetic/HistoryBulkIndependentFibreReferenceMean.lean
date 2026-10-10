import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreMassCompatibility
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreMassFactorization
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceTerm

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreReference
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization (Current Choices)
open HistoryBulkIndependentFibreMass
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
variable (he : PreservesRemainingBands _ e) (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)
include he

theorem reference_compatible_all (r : Reference C outside a e s t c₁ c₂)
    (u : SelectedBulkSample C l) : Compatible C a e u :=
  (fibre_smallCounterpartCompatible_iff C a r.bulk u e he).mpr r.compatible

theorem reference_right_mass_nonzero (r : Reference C outside a e s t c₁ c₂)
    (u : SelectedBulkSample C l) (hc : Compatible C a e u)
    (hu : (selectedBulkPrior C l).mass u≠0) :
    (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).mass (rightAssignment C a e u hc)≠0 :=
  (counterpart_fibreAssignment_mass_ne_zero_iff C a e he r.bulk u r.compatible hc
    (ne_of_gt r.bulk_pos) hu).mpr r.right_mass

def fixedReferenceTerm (K : ℕ) (r : Reference C outside a e s t c₁ c₂)
    (u : SelectedBulkSample C l) (P Q : ℤ) : ℂ :=
  referenceTerm C outside a e he s t c₁ c₂ K r u
    (reference_compatible_all C outside a e he s t c₁ c₂ r u) P Q

def referenceMean (K : ℕ) (r : Reference C outside a e s t c₁ c₂) : ℂ :=
  (selectedBulkPrior C l).cmean (fun u=>mixedMean C.giantCenter C.giant
    (fixedReferenceTerm C outside a e he s t c₁ c₂ K r u))

theorem term_eq_fixedReferenceTerm
    {spectator : PrimeSource}
    (hactual : HistoryBulkIndependentReferenceTerm.SelectedOrderedReferenceEquality C spectator)
    (K : ℕ) (hle : l≤K) (hl : l≤k)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc₁ : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₁≠0)
    (hc₂ : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₂≠0)
    (houtside : ∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q)
    (r : Reference C outside a e s t c₁ c₂) (u : SelectedBulkSample C l)
    (hu : (selectedBulkPrior C l).mass u≠0) (P Q : ℤ) (hp : 0<P) (hq : 0<Q) :
    term C outside a e s t c₁ c₂ u P Q=
      fixedReferenceTerm C outside a e he s t c₁ c₂ K r u P Q := by
  have hc := reference_compatible_all C outside a e he s t c₁ c₂ r u
  simp only [term,hc,dite_true,fixedReferenceTerm]
  exact compatibleTerm_eq_referenceTerm C outside a e he s t c₁ c₂ hactual K hle hl
    ha hc₁ hc₂ houtside r u hc hu
    (reference_right_mass_nonzero C outside a e he s t c₁ c₂ r u hc hu) P Q hp hq

theorem mixedFibreMean_eq_referenceMean
    {spectator : PrimeSource}
    (hactual : HistoryBulkIndependentReferenceTerm.SelectedOrderedReferenceEquality C spectator)
    (K : ℕ) (hle : l≤K) (hl : l≤k)
    (ha : 0 < (selectedNonbulkPrior C l).mass a)
    (hc₁ : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₁≠0)
    (hc₂ : choicesMass C.sources _ (frequencyBound Bs BD Bz k L) l c₂≠0)
    (houtside : ∀q∈outside,∃p : spectator.Sample,(p:ℕ)=q)
    (r : Reference C outside a e s t c₁ c₂) :
    mixedFibreMean C outside a e s t c₁ c₂=referenceMean C outside a e he s t c₁ c₂ K r := by
  rw [mixedFibreMean_eq_weighted]
  have hr : referenceMean C outside a e he s t c₁ c₂ K r=
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass
        (mixedWeight C.giantCenter C.giant) (fun u z=>
          fixedReferenceTerm C outside a e he s t c₁ c₂ K r u
            (mixedP C.giantCenter C.giant z) (mixedQ C.giantCenter C.giant z)) := by
    simp only [referenceMean,mixedMean_eq_weighted,FinitePrior.cmean,
      HistoryBulkFibreReference.originalMean,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]
  rw [hr]
  apply HistoryBulkFibreReference.originalMean_congr
  intro u z hu _
  exact term_eq_fixedReferenceTerm C outside a e he s t c₁ c₂ hactual K hle hl
    ha hc₁ hc₂ houtside r u hu _ _
    (mixedDraw_positive C.giantCenter C.giant z).1 (mixedDraw_positive C.giantCenter C.giant z).2

end Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

end

end OAI
