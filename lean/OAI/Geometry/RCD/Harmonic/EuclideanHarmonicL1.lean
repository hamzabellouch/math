import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicWideExtension
import OAI.Geometry.RCD.Coordinates.NormalizedLocalL2

namespace OAI

/-! # L¹ mass of normalized compact harmonic extensions -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

/-- The normalized L² bound controls the entire L¹ mass of any compact
extension dominated by the model. -/
theorem EuclideanHarmonicModel.extension_l1_le {n : ℕ} {S : ℝ}
    (w : EuclideanHarmonicModel n S) (hS : 0 < S)
    {F : Euclidean n → ℝ} (hF : Continuous F) (hfs : HasCompactSupport F)
    (hs : tsupport F ⊆ ball 0 S) (hb : ∀ x, |F x| ≤ |w.value x|) :
    (∫ x, |F x|) ≤ volume.real (ball (0 : Euclidean n) S) := by
  let B := ball (0 : Euclidean n) S
  have hV : 0 < volume.real B := ENNReal.toReal_pos (measure_ball_pos volume (0 : Euclidean n) hS).ne' measure_ball_ne_top
  have hnorm := normalizeLocalL2_norm_sq volume B measure_ball_ne_top (w.memLp.toLp w.value)
  have he : (∫ x in B, ((w.memLp.toLp w.value) x)^2) = ∫ x in B, (w.value x)^2 := by
    apply integral_congr_ae
    filter_upwards [w.memLp.coeFn_toLp] with x hx
    rw [hx]
  rw [he] at hnorm
  have hN : ‖normalizeLocalL2 volume B measure_ball_ne_top (w.memLp.toLp w.value)‖^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (norm_nonneg _) w.normalized 2
  rw [hnorm] at hN
  have hsq : (∫ x in B, (w.value x)^2) ≤ volume.real B := by
    have hh := mul_le_mul_of_nonneg_left hN hV.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hV.ne',one_mul,mul_one] using hh
  have hzero : ∀ᵐ x ∂(volume : Measure (Euclidean n)), x ∉ B → |F x| = 0 := by
    filter_upwards with x hx
    have hz : F x = 0 := by
      by_contra hn
      exact hx (hs (subset_tsupport F hn))
    simp only [hz,abs_zero]
  have hfi : Integrable (fun x => |F x|) volume := hF.abs.integrable_of_hasCompactSupport hfs.abs
  have hi : IntegrableOn (fun x => (w.value x)^2+1) B volume :=
    w.memLp.integrable_sq.add (integrableOn_const measure_ball_ne_top)
  have hbound : 2*(∫ x in B, |F x|) ≤ (∫ x in B, (w.value x)^2)+volume.real B := by
    calc
      _ = ∫ x in B, 2*|F x| := (integral_const_mul _ _).symm
      _ ≤ ∫ x in B, (w.value x)^2+1 := by
        apply integral_mono_ae (hfi.const_mul 2).integrableOn hi
        filter_upwards with x
        have hh := hb x
        nlinarith [sq_nonneg (|w.value x|-1),sq_abs (w.value x)]
      _ = _ := by rw [integral_add w.memLp.integrable_sq (integrableOn_const measure_ball_ne_top),setIntegral_const,smul_eq_mul,mul_one]
  have heF : (∫ x in B, |F x|) = ∫ x, |F x| := setIntegral_eq_integral_of_ae_compl_eq_zero hzero
  rw [heF] at hbound
  linarith only [hbound,hsq]

end RegularPointCoordinates

end

end OAI
