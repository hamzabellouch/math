import Mathlib

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open scoped Real
namespace PlanarEndpoint

lemma interpolate_energy {e m r A B p : ℝ} (he : 0 ≤ e) (hm : 0 ≤ m)
    (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 2 < p)
    (h1 : e ≤ A*m^(2-2/p)) (h2 : e ≤ B*r^(2/3:ℝ)*m) :
    e ≤ (A+B)*r^(1/3:ℝ)*m^(3/2-1/p) := by
  have hα : 0 < 3/2-1/p := by
    have : 1/p < (1:ℝ)/2 := (div_lt_div_iff₀ (by linarith) (by norm_num)).2 (by linarith)
    linarith
  have heq : (r^(1/3:ℝ)*m^(3/2-1/p))^2 = r^(2/3:ℝ)*m^(2-2/p)*m := by
    have hrid : (r^(1/3:ℝ))^2 = r^(2/3:ℝ) := by
      rw [← Real.rpow_mul_natCast hr.le]
      norm_num
    have hmid : (m^(3/2-1/p))^2 = m^(2-2/p)*m := by
      rw [← Real.rpow_mul_natCast hm,
        ← Real.rpow_add_one' hm (by
          have he : (2-2/p)+1 = 2*(3/2-1/p) := by ring
          rw [he]
          positivity)]
      congr 1
      norm_num
      ring
    rw [mul_pow, hrid, hmid, mul_assoc]
  have hR : 0 ≤ r^(1/3:ℝ)*m^(3/2-1/p) := mul_nonneg
    (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hm _)
  have hAB : 0 ≤ A*B := mul_nonneg hA hB
  have hh := mul_le_mul h1 h2 he (mul_nonneg hA (Real.rpow_nonneg hm _))
  have hh' : e^2 ≤ A*B*(r^(1/3:ℝ)*m^(3/2-1/p))^2 := by
    rw [heq]
    nlinarith only [hh]
  have hp' : A*B ≤ (A+B)^2 := by nlinarith [sq_nonneg (A-B)]
  have hq := mul_le_mul_of_nonneg_right hp' (sq_nonneg (r^(1/3:ℝ)*m^(3/2-1/p)))
  have hn : 0 ≤ (A+B)*(r^(1/3:ℝ)*m^(3/2-1/p)) := mul_nonneg (add_nonneg hA hB) hR
  have := (sq_le_sq₀ he hn).1 (hh'.trans (by nlinarith only [hq]))
  simpa only [mul_assoc] using this

lemma dyadic_rpow_mul (n : ℕ) (a : ℝ) : ((2:ℝ)^n)^a = (2:ℝ)^((n:ℝ)*a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

lemma dyadic_scale (j k : ℕ) (hk : k ≤ j) :
    (2:ℝ)^j * ((2:ℝ)^k)⁻¹ = (2:ℝ)^(j-k) := by
  exact (pow_sub₀ (2:ℝ) (by norm_num) hk).symm

lemma dyadic_width (j k : ℕ) :
    (1/2:ℝ)^(j+k) = ((2:ℝ)^k)⁻¹ / (2:ℝ)^j := by
  rw [one_div, inv_pow, pow_add]
  field_simp

lemma dyadic_decay (k : ℕ) :
    (((2:ℝ)^k)⁻¹)^(1/3:ℝ) = (((2:ℝ)^(-(1/6:ℝ)))^k)^2 := by
  rw [Real.inv_rpow (by positivity), dyadic_rpow_mul, ← Real.rpow_mul_natCast (by positivity),
    ← Real.rpow_mul_natCast (by positivity),
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

end PlanarEndpoint
end

end OAI
