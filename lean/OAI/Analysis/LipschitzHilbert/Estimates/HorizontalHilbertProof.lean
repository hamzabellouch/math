import OAI.Analysis.LipschitzHilbert.Estimates.SharpHilbertThreeHalves

namespace OAI

/-! The classical one-dimensional input required by the manuscript is
proved at the two required exponents. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert
open PacketRepresentation

theorem horizontalHilbertInput_proved : HorizontalHilbertInput := by
  obtain ⟨C,hC,hthree⟩ := sharpHilbert_uniform_three_halves
  obtain ⟨D,hD,hfour⟩ := sharpHilbert_uniform_fourth
  let B := C+D+1
  have hB : 0<B := by dsimp [B]; positivity
  have hCB : C≤B := by dsimp [B]; linarith
  have hDpow : D≤B^4 := by
    have hsmall : D≤(D+1)^4 := by nlinarith [sq_nonneg D,pow_nonneg hD 3,pow_nonneg hD 4]
    exact hsmall.trans (pow_le_pow_left₀ (by positivity) (by dsimp [B]; linarith) 4)
  refine ⟨B,hB,?_⟩
  intro p hp r R hr hrR f
  rcases hp with rfl | rfl
  · obtain ⟨hi,he⟩ := hthree r R hr hrR f
    refine ⟨hi,he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hC.le hCB (by norm_num))
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
  · obtain ⟨hi,he⟩ := hfour r R hr hrR f
    simp only [Real.rpow_ofNat]
    refine ⟨hi,he.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hDpow (integral_nonneg fun x => by positivity)

end LipschitzHilbert

end

end OAI
