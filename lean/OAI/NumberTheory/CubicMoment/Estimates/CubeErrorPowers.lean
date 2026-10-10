import OAI.NumberTheory.CubicMoment.Estimates.CubeUniformError

namespace OAI

/-! The logarithmic cutoff in H=L²/A suppresses the bounded cube-lattice
error. This is the precise elementary scale comparison used below. -/
noncomputable section
namespace CubicFirstMoment

lemma cube_lattice_error_scale {A L z : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hz : 0 < z) (a k : ℕ) (hcut : A ≤ L^2/z^(3*(a+k))) :
    A*L*z^a ≤ A^(2/3:ℝ)*L^(5/3:ℝ)/z^k := by
  have hA3 : (A^(1/3:ℝ))^3 = A := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hA.le]
    norm_num
  have hL3 : (L^(2/3:ℝ))^3 = L^2 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hL.le]
    norm_num
  have hpow : (z^(a+k))^3 = z^(3*(a+k)) := by rw [← pow_mul]; congr 1; omega
  have hsmall : A^(1/3:ℝ)*z^(a+k) ≤ L^(2/3:ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (3:ℕ) ≠ 0)).mp
    rw [mul_pow,hA3,hpow,hL3]
    exact (le_div_iff₀ (pow_pos hz _)).mp hcut
  have hAexp : A^(2/3:ℝ)*A^(1/3:ℝ) = A := by rw [← Real.rpow_add hA]; norm_num
  have hLexp : L*L^(2/3:ℝ) = L^(5/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    norm_num
  apply (le_div_iff₀ (pow_pos hz k)).mpr
  calc
    A*L*z^a*z^k = (A^(2/3:ℝ)*L)*(A^(1/3:ℝ)*z^(a+k)) := by
      rw [pow_add]
      calc
        _ = A*(L*z^a*z^k) := by ring
        _ = (A^(2/3:ℝ)*A^(1/3:ℝ))*(L*z^a*z^k) := by rw [hAexp]
        _ = _ := by ring
    _ ≤ (A^(2/3:ℝ)*L)*L^(2/3:ℝ) := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := by rw [mul_assoc,hLexp]

end CubicFirstMoment

end

end OAI
