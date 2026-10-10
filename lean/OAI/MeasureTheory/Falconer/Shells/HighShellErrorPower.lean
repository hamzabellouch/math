import OAI.MeasureTheory.Falconer.Shells.HighShellRadialBounds

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem high_shell_error_power (N a : ℕ) (hN : 1 ≤ N) {v : ℝ} (hv : v ≤ N) (T : ℝ) :
    (2:ℝ)^(-(a:ℝ)) * (2*(((2:ℝ)^N)^(-((T+3)/2)))^2 *
      (volume.restrict (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)))).real univ) ≤
        ((2:ℝ)^N)^(-T) := by
  let R : ℝ := (2:ℝ)^N
  have hR : 0 < R := by dsimp [R]; positivity
  have hR2 : 2 ≤ R := by
    dsimp [R]
    exact_mod_cast (show 2^1 ≤ 2^N from Nat.pow_le_pow_right (by omega) hN)
  have houter : (2:ℝ)^(-(a:ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show -(a:ℝ) ≤ 0 from neg_nonpos.mpr (Nat.cast_nonneg a))
  have hlength : (volume.restrict (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)))).real univ ≤ 2*R := by
    rw [measureReal_def,Measure.restrict_apply_univ,Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)))]
    have hp : (2:ℝ)^(v+1) ≤ 2*R := by
      rw [Real.rpow_add (by norm_num),Real.rpow_one,mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hv
    linarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (v-1)]
  have he : (R^(-((T+3)/2)))^2 = R^(-(T+3)) := by
    rw [← Real.rpow_mul_natCast hR.le]
    congr 1
    norm_num
  change (2:ℝ)^(-(a:ℝ))*(2*(R^(-((T+3)/2)))^2*_) ≤ R^(-T)
  rw [he]
  calc
    _ ≤ 1*(2*R^(-(T+3))*(2*R)) :=
      mul_le_mul houter (mul_le_mul_of_nonneg_left hlength (by positivity))
        (by positivity) (by norm_num)
    _ = 4*R*R^(-(T+3)) := by ring
    _ ≤ R^3*R^(-(T+3)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (R-2)]
    _ = R^(-T) := by
      rw [← Real.rpow_natCast R 3,← Real.rpow_add hR]
      congr 1
      norm_num

end PlanarFalconer

end OAI
