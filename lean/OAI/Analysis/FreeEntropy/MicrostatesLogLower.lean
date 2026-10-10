import OAI.Analysis.FreeEntropy.GaussianAffineVolume

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace FiniteEntropySeparation
 theorem normalized_log_lower (n d : ℕ) (hd : 0<d) {u : ℝ} (hu : 0<u) {v : ℝ≥0∞}
    (hvtop : v≠⊤) (hv : ENNReal.ofReal ((Real.sqrt u/Real.sqrt d)^(n*d*d)/2)≤v) :
    (((n:ℝ)/2*Real.log u-Real.log 2 : ℝ):EReal) ≤
      ((((d:ℝ)^2)⁻¹:ℝ):EReal)*v.log+(((n:ℝ)/2*Real.log d:ℝ):EReal) := by
  have hd' : 0<(d:ℝ) := Nat.cast_pos.mpr hd
  have hr : 0<Real.sqrt u/Real.sqrt d := div_pos (Real.sqrt_pos.mpr hu) (Real.sqrt_pos.mpr hd')
  let q := (Real.sqrt u/Real.sqrt d)^(n*d*d)/2
  have hq : 0<q := by dsimp [q]; positivity
  have hqv : q≤v.toReal := by
    have h := ENNReal.toReal_mono hvtop hv
    rwa [ENNReal.toReal_ofReal hq.le] at h
  have hvpos : 0<v.toReal := hq.trans_le hqv
  rw [ENNReal.log_pos_real' hvpos,← EReal.coe_mul,← EReal.coe_add,EReal.coe_le_coe_iff]
  have hl : Real.log q ≤ Real.log v.toReal := Real.log_le_log hq hqv
  have he : Real.log q = (n:ℝ)*(d:ℝ)^2/2*(Real.log u-Real.log d)-Real.log 2 := by
    dsimp [q]
    rw [Real.log_div (pow_ne_zero _ hr.ne') (by norm_num),Real.log_pow,
      Real.log_div (Real.sqrt_pos.mpr hu).ne' (Real.sqrt_pos.mpr hd').ne',Real.log_sqrt hu.le,Real.log_sqrt hd'.le]
    push_cast
    ring
  rw [he] at hl
  have hmul := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr (sq_nonneg (d:ℝ)))
  have hcalc : ((d:ℝ)^2)⁻¹*((n:ℝ)*(d:ℝ)^2/2*(Real.log u-Real.log d)-Real.log 2)+
      (n:ℝ)/2*Real.log d=(n:ℝ)/2*Real.log u-Real.log 2/((d:ℝ)^2) := by
    field_simp; ring
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hlog : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hh : Real.log 2/((d:ℝ)^2) ≤ Real.log 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd')).2
    nlinarith [sq_nonneg ((d:ℝ)-1),mul_nonneg hlog (show 0≤(d:ℝ)^2-1 by nlinarith)]
  linarith
end FiniteEntropySeparation

end

end OAI
