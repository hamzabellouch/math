import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkIndependentFibreReferenceLaws

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped Classical
namespace Ostmann.Arithmetic.HistoryBulkIndependentFibreReference
open Construction Conclusion HistoryBulkSourceDisintegration HistoryBulkFibreOriginalReference
open HistoryGiantReferenceMean
open HistoryGiantOriginalMeanFactorization (Current Choices)
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}
variable (C : InitialSourceChoice d Bs BD Bz k L E) (outside : List ℕ)
variable (a : SelectedNonbulkSample C l) (e : RemainingPermutation (k:=k) (L:=L) (l:=l))
variable (s t : ℤ) (c₁ c₂ : Choices (l:=l) C)

structure Reference where
  bulk : SelectedBulkSample C l
  draw : MixedDraw C.giantCenter C.giant
  compatible : Compatible C a e bulk
  bulk_pos : 0 < (selectedBulkPrior C l).mass bulk
  draw_pos : 0 < mixedWeight C.giantCenter C.giant draw
  term_ne_zero : compatibleTerm C outside a e s t c₁ c₂ bulk compatible
    (mixedP C.giantCenter C.giant draw) (mixedQ C.giantCenter C.giant draw)≠0
  right_mass : (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).mass
    (rightAssignment C a e bulk compatible)≠0
  supported : Supported C outside a e s t c₁ c₂ bulk compatible
    (mixedP C.giantCenter C.giant draw) (mixedQ C.giantCenter C.giant draw)

theorem mixedFibreMean_eq_zero_or_reference
    (ha : 0 < (selectedNonbulkPrior C l).mass a) :
    mixedFibreMean C outside a e s t c₁ c₂=0 ∨
      Nonempty (Reference C outside a e s t c₁ c₂) := by
  rw [mixedFibreMean_eq_weighted]
  rcases HistoryBulkFibreReference.originalMean_eq_zero_or_reference
      (selectedBulkPrior C l).mass (mixedWeight C.giantCenter C.giant)
      (fun u r=>term C outside a e s t c₁ c₂ u
        (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r))
      (selectedBulkPrior C l).mass_nonneg (mixedWeight_nonneg C.giantCenter C.giant)
      (fun _ _=>True) (fun _ _ _ _ _=>True.intro) with
    hz | ⟨u,r,hu,hr,hne,_⟩
  · exact Or.inl hz
  · by_cases hc : Compatible C a e u
    · have ht : compatibleTerm C outside a e s t c₁ c₂ u hc
          (mixedP C.giantCenter C.giant r) (mixedQ C.giantCenter C.giant r)≠0 := by
        simpa only [term,hc,dite_true] using hne
      have hy : (assignmentPrior C.sources (Current (k:=k) (L:=L) (l:=l))).mass
          (rightAssignment C a e u hc)≠0 := by
        intro hzero
        have hz := weighted_compatibleTerm_zero_of_right_mass_zero C outside a e s t c₁ c₂
          u hc (ne_of_gt (fibreAssignment_mass_pos C a u ha hu)) hzero r
        exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr)) ht) hz
      exact Or.inr ⟨⟨u,r,hc,hu,hr,ht,hy,
        compatibleTerm_ne_zero_supported C outside a e s t c₁ c₂ u hc _ _ ht⟩⟩
    · exact (hne (by simp only [term,hc,dite_false])).elim

end Ostmann.Arithmetic.HistoryBulkIndependentFibreReference

end

end OAI
