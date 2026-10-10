import OAI.NumberTheory.Jacobsthal.Estimates.RieszCauchy

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Set

lemma arctan_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h := intervalIntegral.integral_mono_on (a := 0) (b := x) hx
    integrable_inv_one_add_sq.intervalIntegrable (intervalIntegrable_const (c := (1:ℝ)))
    (fun t _ => show (1+t^2)⁻¹ ≤ 1 by
      rw [← one_div]
      exact (div_le_iff₀ (by positivity : 0 < 1+t^2)).mpr (by nlinarith [sq_nonneg t]))
  rw [integral_inv_one_add_sq,Real.arctan_zero,sub_zero] at h
  simpa using h

lemma rieszMajorant_upper_tail {T : ℝ} (hT : 0 < T) :
    (∫ t in Ici T, (4:ℝ)/(1+t^2)) ≤ 4/T := by
  rw [integral_Ici_eq_integral_Ioi]
  simp only [div_eq_mul_inv,integral_const_mul,integral_Ioi_inv_one_add_sq]
  have hi := Real.arctan_inv_of_pos hT
  simp only [div_eq_mul_inv] at hi
  rw [← hi]
  exact mul_le_mul_of_nonneg_left (arctan_le_self_nonneg (inv_nonneg.mpr hT.le)) (by norm_num)

lemma rieszMajorant_lower_tail {T : ℝ} (hT : 0 < T) :
    (∫ t in Iic (-T), (4:ℝ)/(1+t^2)) ≤ 4/T := by
  have he : (∫ t in Iic (-T), (4:ℝ)/(1+t^2)) = ∫ t in Ici T, (4:ℝ)/(1+t^2) := by
    rw [integral_Ici_eq_integral_Ioi]
    simp only [div_eq_mul_inv,integral_const_mul,integral_Iic_inv_one_add_sq,
      integral_Ioi_inv_one_add_sq,Real.arctan_neg]
    ring
  rw [he]
  exact rieszMajorant_upper_tail hT

lemma rieszMajorant_interval_le (T : ℝ) :
    (∫ t in (-T)..T, (4:ℝ)/(1+t^2)) ≤ 4*Real.pi := by
  simp only [div_eq_mul_inv,intervalIntegral.integral_const_mul,integral_inv_one_add_sq,Real.arctan_neg]
  have h := Real.arctan_lt_pi_div_two T
  linarith

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
