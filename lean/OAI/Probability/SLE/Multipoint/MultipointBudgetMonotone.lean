import OAI.Probability.SLE.Multipoint.MultipointGlobalDiscount
import OAI.Probability.SLE.Multipoint.MultipointInitialParameters

namespace OAI

/-! The fixed-order constant remains valid after discarding constraints
whose targets already exceed their caps. -/

noncomputable section
open Set
open scoped BigOperators

namespace SLEExactGauge.Multipoint

lemma allPatternYoungConstant_mono {ι : Type*} [DecidableEq ι] {κ : ℝ}
    (hκ : 0 < κ) (hκ8 : κ < 8) {I J : Finset ι} (hIJ : I ⊆ J) :
    allPatternYoungConstant κ I ≤ allPatternYoungConstant κ J := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.powerset_mono.mpr hIJ)
  exact fun s _ _ => (patternYoungConstant_pos hκ hκ8 s).le

lemma allPatternYoungConstant_map {ι ν : Type*} [DecidableEq ι] [DecidableEq ν]
    (κ : ℝ) (f : ι ↪ ν) (I : Finset ι) :
    allPatternYoungConstant κ (I.map f) = allPatternYoungConstant κ I := by
  classical
  unfold allPatternYoungConstant
  rw [Finset.map_eq_image,Finset.powerset_image,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s _
    simp only [patternYoungConstant,Finset.card_image_of_injective s f.injective]
  · exact Finset.image_injOn_powerset_of_injOn (fun _ _ _ _ h => f.injective h)

lemma uniformDiscountBudget_map {ι ν : Type*} [DecidableEq ι] [DecidableEq ν]
    (κ β : ℝ) (f : ι ↪ ν) (I : Finset ι) :
    uniformDiscountBudget κ β (I.map f) = uniformDiscountBudget κ β I := by
  simp only [uniformDiscountBudget,allPatternYoungConstant_map,Finset.offDiag_card,Finset.card_map]

lemma uniformDiscountBudget_mono {ι : Type*} [DecidableEq ι] {κ : ℝ}
    (hκ : 0 < κ) (hκ8 : κ < 8) {I J : Finset ι} (hIJ : I ⊆ J) :
    uniformDiscountBudget κ (sourceBeta κ) I ≤ uniformDiscountBudget κ (sourceBeta κ) J := by
  obtain ⟨_,hβ,_,_,hdecay⟩ := source_parameters hκ hκ8
  have hpair := (interactionBudget_pos (by norm_num : (0 : ℝ) < 2) hdecay).le
  have hcard : (I.card : ℝ) ≤ J.card := by exact_mod_cast Finset.card_le_card hIJ
  have hoff : (I.offDiag.card : ℝ) ≤ J.offDiag.card := by
    exact_mod_cast Finset.card_le_card (Finset.offDiag_mono hIJ)
  unfold uniformDiscountBudget
  apply mul_le_mul_of_nonneg_left _ hκ.le
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcard (by positivity)) (singleDriftConstant_pos hκ hκ8).le
  · exact mul_le_mul (allPatternYoungConstant_mono hκ hκ8 hIJ)
      (mul_le_mul_of_nonneg_right hoff hpair) (mul_nonneg (Nat.cast_nonneg _) hpair)
      (allPatternYoungConstant_pos hκ hκ8 J).le

end SLEExactGauge.Multipoint

end

end OAI
