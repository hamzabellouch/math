import OAI.NumberTheory.TwoPoint.Fourier.MajorArcGlobalRate
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionSummability

namespace OAI

/-! The correction and character factors fit the exact error exponents
of corrected MRT Theorem 1.7 at the common parameter. -/
namespace TwoPointCorrelations

open Filter

lemma major_arc_inverse_parameter_error {W : ℝ} (hW : 1 ≤ W) :
    W⁻¹ ≤ majorArcWorkingError W ∧ W^(-5/4:ℝ) ≤ majorArcWorkingError W := by
  have hW0 : 0 < W := by linarith
  have hi : W⁻¹ ≤ majorArcWorkingError W := by
    calc
      _ = W^(-1:ℝ) := (Real.rpow_neg_one W).symm
      _ ≤ W^(-1/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hW (by norm_num)
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hW0.le _)
        (by linarith [Real.log_nonneg hW])
  refine ⟨hi,?_⟩
  exact (Real.rpow_le_rpow_of_exponent_le hW (show (-5/4:ℝ) ≤ -1 by norm_num)).trans
    (by simpa only [Real.rpow_neg_one] using hi)

theorem major_arc_corrected_published_rate (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ H M : ℝ, 1 ≤ Real.log H →
      1 ≤ Real.log (Real.log H) → 0 ≤ M →
      let W := majorArcParameter L H M
      mrtCorrectionBound*(4*(1+4*Real.pi)*(4*C*(Real.sqrt W*(1+Real.log W))*
        (Real.exp (-2*M/5)+Real.sqrt (Real.log L/L^(1/80:ℝ))+W⁻¹)+3/W)+
        5*W^(-5/4:ℝ)) ≤
      (2500*mrtCorrectionBound*(C+1)*(1+4*Real.pi))*
        (Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)) := by
  filter_upwards [major_arc_weighted_energy_rate,major_arc_parameter_rate,
    eventually_ge_atTop (1:ℝ)] with L henergy hparameter hL
  intro H M hH hHH hM
  dsimp only
  let W := majorArcParameter L H M
  let E := Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)
  obtain ⟨hW,hWH,hWL,hWM⟩ := major_arc_parameter_bounds hL hH hM
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hk : majorArcWorkingError W ≤ 21*E := by
    have hh := hparameter H M hH hHH hM
    have he := Real.exp_pos (-M/20)
    have hl : 0 ≤ L^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    have hshort : 0 ≤ Real.log (Real.log H)/Real.log H := by positivity
    rw [mul_div_assoc] at hh
    dsimp only [E,W]
    linarith
  have he : Real.sqrt W*(1+Real.log W)*
      (Real.exp (-2*M/5)+Real.sqrt (Real.log L/L^(1/80:ℝ))+W⁻¹) ≤ 122*E := by
    have hh := henergy W M hW hWL hM hWM
    have hexp := Real.exp_pos (-M/20)
    have hl : 0 ≤ L^(-1/700:ℝ) := Real.rpow_nonneg (by linarith) _
    have hshort : 0 ≤ Real.log (Real.log H)/Real.log H := by positivity
    dsimp only [E] at *
    linarith
  obtain ⟨hinv,hpow⟩ := major_arc_inverse_parameter_error hW
  have hi : 1/W ≤ 21*E := by simpa only [one_div] using hinv.trans hk
  have hp : W^(-5/4:ℝ) ≤ 21*E := hpow.trans hk
  have hb : 0 < mrtCorrectionBound := Real.exp_pos _
  have ht : 0 < 1+4*Real.pi := by positivity
  calc
    _ ≤ mrtCorrectionBound*(4*(1+4*Real.pi)*(4*C*(122*E)+3*(21*E))+5*(21*E)) := by
      apply mul_le_mul_of_nonneg_left _ hb.le
      have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*C by positivity)
      have hm' : 4*C*(Real.sqrt W*(1+Real.log W))*
          (Real.exp (-2*M/5)+Real.sqrt (Real.log L/L^(1/80:ℝ))+W⁻¹) ≤ 4*C*(122*E) := by
        simpa only [mul_assoc] using hm
      have hmain := mul_le_mul_of_nonneg_left
        (add_le_add hm' (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤3)))
        (show 0 ≤ 4*(1+4*Real.pi) by positivity)
      have htail := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤5)
      have hs := add_le_add hmain htail
      convert hs using 1
      ring
    _ ≤ _ := by
      have hc : (4*(1+4*Real.pi)*(4*C*122+3*21)+5*21) ≤
          2500*(C+1)*(1+4*Real.pi) := by nlinarith [Real.pi_pos]
      have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hE) hb.le
      convert hm using 1 <;> ring

lemma major_arc_rate_volume {A C B x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : C*A ≤ B) : C*x*y*A ≤ B*x*y := by
  calc
    _ = (C*A)*x*y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h hx) hy

end TwoPointCorrelations

end OAI
