import OAI.Probability.MatroidProphet.Residual.MaskUnion

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [DecidableEq α]

lemma residualDelta_nonneg : 0 ≤ residualDelta := by unfold residualDelta; positivity

lemma bitsExpectation_residualBad_delta (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (1000 * Real.log densityThreshold / densityThreshold * V.card))
    (hn : densityThreshold ≤ (V.card : ℝ)) :
    bitsExpectation q V (residualBadIndicator F (residualDelta * V.card)) ≤ residualDelta := by
  have htail := bitsExpectation_residualBad_le q hq0 hqhalf V F hF (residualDelta * V.card)
  have hmul := mul_le_mul_of_nonneg_right hcard
    (Real.exp_nonneg (-(residualDelta * V.card) * Real.log 2))
  apply htail.trans (hmul.trans ?_)
  rw [← Real.exp_add]
  convert residual_tail_constant (V.card : ℝ) hn using 1
  congr 1
  ring

lemma capturedResidual_le
    {α : Type u_1} [DecidableEq α] (V S R : Finset α) (F : Finset (Finset α))
    (hS : S ⊆ V) (hR : R ∈ F) (hRS : R ⊆ S) :
    (R.card : ℝ) ≤ residualDelta * V.card +
      (V.card : ℝ) * residualBadIndicator F (residualDelta * V.card) S := by
  classical
  have hcard : (R.card : ℝ) ≤ V.card := by exact_mod_cast Finset.card_le_card (hRS.trans hS)
  have hδ : 0 ≤ residualDelta * (V.card : ℝ) := mul_nonneg residualDelta_nonneg (Nat.cast_nonneg _)
  by_cases hsmall : (R.card : ℝ) ≤ residualDelta * V.card
  · have hind : 0 ≤ residualBadIndicator F (residualDelta * V.card) S := by
      unfold residualBadIndicator
      split_ifs <;> norm_num
    nlinarith [mul_nonneg (Nat.cast_nonneg V.card) hind]
  · have hbad : residualBad F (residualDelta * V.card) S := ⟨R, hR, lt_of_not_ge hsmall, hRS⟩
    simp only [residualBadIndicator, hbad, ite_true, mul_one]
    linarith

lemma tripleMask_residual_error_le
    (p q r : α → ℝ) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (hpq : ∀ e, p e + (1 - p e) * q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (1000 * Real.log densityThreshold / densityThreshold * V.card))
    (hn : densityThreshold ≤ (V.card : ℝ))
    (error : Finset α → Finset α → Finset α → ℝ)
    (herror : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V,
      error D C T ≤ residualDelta * V.card + (V.card : ℝ) *
        residualBadIndicator F (residualDelta * V.card) (D ∪ C)) :
    bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (error D C))) ≤
      2 * residualDelta * V.card := by
  have hpq0 : ∀ e, 0 ≤ p e + (1 - p e) * q e := by
    intro e
    exact add_nonneg (hp0 e) (mul_nonneg (sub_nonneg.mpr (hp1 e)) (hq0 e))
  have hbad := bitsExpectation_residualBad_delta (fun e => p e + (1 - p e) * q e)
    hpq0 hpq V F hF hcard hn
  calc
    _ ≤ bitsExpectation p V (fun D => bitsExpectation q V (fun C => bitsExpectation r V (fun _T =>
          residualDelta * V.card + (V.card : ℝ) * residualBadIndicator F (residualDelta * V.card) (D ∪ C)))) := by
      apply bitsExpectation_mono p hp0 hp1
      intro D hD
      apply bitsExpectation_mono q hq0 hq1
      intro C hC
      exact bitsExpectation_mono r hr0 hr1 V (fun T hT => herror D hD C hC T hT)
    _ = residualDelta * V.card + (V.card : ℝ) * bitsExpectation
        (fun e => p e + (1 - p e) * q e) V (residualBadIndicator F (residualDelta * V.card)) := by
      simp_rw [bitsExpectation_const, bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_const]
      rw [bitsExpectation_union]
    _ ≤ residualDelta * V.card + (V.card : ℝ) * residualDelta :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad (Nat.cast_nonneg V.card))
    _ = _ := by ring

end MatroidProphet

end OAI
