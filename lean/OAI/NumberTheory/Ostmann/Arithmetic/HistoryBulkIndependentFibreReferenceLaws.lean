import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceDefs

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreReference
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization (Current Choices history counterpart)
open HistoryDiagonalCorrectedOriginalMean hiding originalMixedMean
open HistorySignedXiTransport
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
variable (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)

theorem mixedMean_term_eq (u : SelectedBulkSample C l) :
    mixedMean C.giantCenter C.giant (term C outside a e s t c₁ c₂ u)=
      if hc : Compatible C a e u then
        HistoryDiagonalCorrectedOriginalMean.originalMixedMean C outside (fibreAssignment C a u)
          (rightAssignment C a e u hc) s t c₁ c₂ else 0 := by
  by_cases hc : Compatible C a e u
  · have hf : term C outside a e s t c₁ c₂ u=compatibleTerm C outside a e s t c₁ c₂ u hc := by
      funext P Q
      simp only [term,hc,dite_true]
    rw [hf]
    simp only [hc,dite_true]
    rfl
  · simp only [term,hc,dite_false,mixedMean,FinitePrior.cmean,mul_zero,Finset.sum_const_zero]

theorem mixedFibreMean_eq_weighted :
    mixedFibreMean C outside a e s t c₁ c₂=
      HistoryBulkFibreReference.originalMean (selectedBulkPrior C l).mass
        (mixedWeight C.giantCenter C.giant)
        (fun u r=>term C outside a e s t c₁ c₂ u
          (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r)) := by
  simp only [mixedFibreMean,mixedMean_eq_weighted,FinitePrior.cmean,
    HistoryBulkFibreReference.originalMean,Complex.ofReal_mul,Finset.mul_sum,mul_assoc]

theorem compatibleTerm_ne_zero_supported (u : SelectedBulkSample C l)
    (hc : Compatible C a e u) (P Q : ℤ)
    (hne : compatibleTerm C outside a e s t c₁ c₂ u hc P Q≠0) :
    Supported C outside a e s t c₁ c₂ u hc P Q := by
  have hh : supportedHistoryPairXi d (frequencyBound Bs BD Bz k L) outside
      (bulkSize k L/2) (bulkSize k L/2) C.scale C.bulkBin C.spectatorBin C.giantCenter
      (history C (fibreAssignment C a u) s P Q c₁)
      (history C (rightAssignment C a e u hc) t P Q c₂)≠0 :=
    (mul_ne_zero_iff.mp hne).2
  by_contra hs
  exact hh (HistorySignedResidues.supportedHistoryPairXi_eq_zero_of_not _ _ _ _ _ _ _ _ _ _ _ hs)

theorem weighted_compatibleTerm_zero_of_right_mass_zero
    (u : SelectedBulkSample C l) (hc : Compatible C a e u)
    (hx : (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).mass (fibreAssignment C a u)≠0)
    (hy : (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).mass (rightAssignment C a e u hc)=0)
    (r : MixedDraw C.giantCenter C.giant) :
    (mixedWeight C.giantCenter C.giant r:ℂ)*
      compatibleTerm C outside a e s t c₁ c₂ u hc
        (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r)=0 := by
  have hsmall := smallAssignment_mass_zero_of_right_mass_zero C (fibreAssignment C a u)
    (rightAssignment C a e u hc) hx (counterpartCurrentAssignment_outer C _ e hc) hy
  have hz := weighted_counterpart_zero_of_small_mass_zero C (rightAssignment C a e u hc)
    hsmall r.1.val r.2
  simp only [mixedWeight,mixedP,mixedQ,compatibleTerm,sourceIntegrand,multiplier,Complex.ofReal_mul]
  have halg (v b s q f : ℂ) (h : v*q=0) : (v*b)*((s*q)*f)=0 := by
    calc
      _ = (v*q)*(b*s*f) := by ring
      _ = 0 := by rw [h,zero_mul]
  exact halg _ _ _ _ _ hz

end Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

end

end OAI
