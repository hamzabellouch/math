import OAI.MeasureTheory.Falconer.Estimates.ParallelMean

namespace OAI

/-! # Scale cancellation and absorption for the parallel-test average -/

namespace Falconer.Regularization

theorem parallel_mean_scale_identity {R : ℝ} (hR : 0 < R)
    (d : ℕ) (s sig K D n : ℝ) (p : ℕ) :
    2*R^sig*(3*((2*R^(500*sig))/(2:ℝ)^p))^s*((2:ℝ)^p)^s*D*
        (1+(2:ℝ)^s*n)*R^(K+2*((d:ℝ)+1)*sig) =
      (2*(6:ℝ)^s*D*(1+(2:ℝ)^s*n))*R^(K+(2*((d:ℝ)+1)+1+500*s)*sig) := by
  have hc := parallel_mean_width_cancellation (show 0 ≤ 2*R^(500*sig) by positivity) p (s := s)
  have he : 3*(2*R^(500*sig)) = 6*R^(500*sig) := by ring
  calc
    _ = 2*R^sig*((3*((2*R^(500*sig))/(2:ℝ)^p))^s*((2:ℝ)^p)^s)*D*
        (1+(2:ℝ)^s*n)*R^(K+2*((d:ℝ)+1)*sig) := by ring
    _ = 2*R^sig*((6:ℝ)^s*R^(500*sig*s))*D*(1+(2:ℝ)^s*n)*R^(K+2*((d:ℝ)+1)*sig) := by
      rw [hc,he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 6) (by positivity),← Real.rpow_mul hR.le]
    _ = (2*(6:ℝ)^s*D*(1+(2:ℝ)^s*n))*(R^sig*R^(500*sig*s)*R^(K+2*((d:ℝ)+1)*sig)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hR,← Real.rpow_add hR]
      congr 2
      ring

theorem parallel_coefficient_bound {D s n : ℝ} (hD : 0 ≤ D) (_hn : 0 ≤ n)
    {N : ℕ} (hnN : n ≤ N) :
    2*(6:ℝ)^s*D*(1+(2:ℝ)^s*n) ≤
      (2*(6:ℝ)^s*D*(1+(2:ℝ)^s))*(1+2*(N:ℝ)) := by
  have hp : 0 ≤ (2:ℝ)^s := by positivity
  have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hh : 1+(2:ℝ)^s*n ≤ (1+(2:ℝ)^s)*(1+2*(N:ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hnN hp,mul_nonneg hp hN]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*(6:ℝ)^s*D by positivity)

theorem one_add_power_absorb {R E sig : ℝ} (hR : 1 ≤ R) (hE : 0 ≤ E)
    (htwo : 2 ≤ R^sig) : 1+R^E ≤ R^(E+sig) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hp : 1 ≤ R^E := Real.one_le_rpow hR hE
  calc
    _ ≤ 2*R^E := by linarith
    _ ≤ R^sig*R^E := mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = _ := by rw [← Real.rpow_add hRp]; congr 1; ring

end Falconer.Regularization

end OAI
