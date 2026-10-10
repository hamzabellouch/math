import OAI.Geometry.Relativity.CKS.BendingDerivative

namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter
open scoped Topology ContDiff

lemma bendingV_deriv {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    deriv (bendingV R) r =
      (phi (r/R) + r * (deriv phi (r/R)/R)) * xi (r/R^2) +
        r * phi (r/R) * (deriv xi (r/R^2)/R^2) := by
  have hp := (phi_smooth.contDiffAt (isOpen_Ioi.mem_nhds (div_pos hr hR))).differentiableAt (by simp)
  have hpd := hp.hasDerivAt.comp r ((hasDerivAt_id r).div_const R)
  have hxd := (xi_smooth.differentiable (by simp) (r/R^2)).hasDerivAt.comp r
    ((hasDerivAt_id r).div_const (R^2))
  convert! (((hasDerivAt_id r).mul hpd).mul hxd).deriv using 1
  simp
  ring

lemma bendingV_reduced_deriv {R r : ℝ} (hR : 0 < R) (hr : 0 < r) :
    r * deriv (bendingV R) r - bendingV R r =
      r * ((r/R) * deriv phi (r/R)) * xi (r/R^2) +
        r * phi (r/R) * ((r/R^2) * deriv xi (r/R^2)) := by
  rw [bendingV_deriv hR hr]
  unfold bendingV
  ring

lemma base_tail {R r : ℝ} (hR : 12 ≤ R) (hr : R^2 ≤ r) :
    r * phi (r/R) = R^3/r^2 := by
  have hRp : 0 < R := by linarith
  have hrp : 0 < r := lt_of_lt_of_le (sq_pos_of_pos hRp) hr
  have hx : 12 ≤ r/R := (le_div_iff₀ hRp).mpr (by nlinarith)
  rw [phi_tail hx]
  field_simp

lemma base_tail_le_one {R r : ℝ} (hR : 12 ≤ R) (hr : R^2 ≤ r) :
    r * phi (r/R) ≤ 1 := by
  have hRp : 0 < R := by linarith
  have hrp : 0 < r := lt_of_lt_of_le (sq_pos_of_pos hRp) hr
  rw [base_tail hR hr]
  apply (div_le_iff₀ (sq_pos_of_pos hrp)).mpr
  have hR1 : 1 ≤ R := by linarith
  have hrr : R^2 * R^2 ≤ r*r := mul_self_le_mul_self (sq_nonneg R) hr
  have hp := mul_le_mul_of_nonneg_left hR1 (pow_nonneg hRp.le 3)
  nlinarith

lemma v_le_sqrt (z : ℝ) (hz : 0 ≤ z) : z ≤ Real.sqrt (1+z^2) := by
  apply (Real.le_sqrt hz (by positivity)).mpr
  nlinarith
lemma one_le_sqrt (z : ℝ) : 1 ≤ Real.sqrt (1+z^2) := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [sq_nonneg z]

theorem bendingV_first_scaled : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 12 ≤ R →
    ∀ r : ℝ, 0 < r → |r * deriv (bendingV R) r - bendingV R r| ≤
      C * Real.sqrt (1 + (bendingV R r)^2) := by
  obtain ⟨C,hC,hphi⟩ := phi_scaled_deriv_bound
  obtain ⟨K,hK,hxi⟩ := xi_scaled_deriv_bound
  have hC0 : 0 ≤ C := by linarith
  refine ⟨C+K,add_nonneg hC0 hK,fun R hR r hr => ?_⟩
  have hRp : 0 < R := by linarith
  have hv0 := bendingV_nonneg hRp hr
  have hvs := v_le_sqrt _ hv0
  have hs1 := one_le_sqrt (bendingV R r)
  have hmain : |r * ((r/R) * deriv phi (r/R)) * xi (r/R^2)| ≤ C * bendingV R r := by
    rw [abs_mul,abs_mul,abs_of_pos hr,abs_of_nonneg (xi_nonneg _)]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hphi (r/R) (div_pos hr hRp)) hr.le) (xi_nonneg (r/R^2))
    convert! hh using 1
    simp only [bendingV]
    ring
  have hcut : |r * phi (r/R) * ((r/R^2) * deriv xi (r/R^2))| ≤ K * Real.sqrt (1+(bendingV R r)^2) := by
    by_cases hc : r ≤ R^2
    · have hy : r/R^2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hRp)).mpr (by simpa using hc)
      rw [xi_deriv_initial hy,mul_zero,mul_zero,abs_zero]
      exact mul_nonneg hK (Real.sqrt_nonneg _)
    · rw [abs_mul,abs_mul,abs_of_pos hr,abs_of_pos (phi_pos (div_pos hr hRp))]
      calc
        _ ≤ r * phi (r/R) * K := mul_le_mul_of_nonneg_left (hxi _) (mul_nonneg hr.le (phi_pos (div_pos hr hRp)).le)
        _ ≤ K := by nlinarith [base_tail_le_one hR (le_of_not_ge hc)]
        _ ≤ K * Real.sqrt (1+(bendingV R r)^2) := by nlinarith
  rw [bendingV_reduced_deriv hRp hr]
  calc
    _ ≤ |r * ((r/R) * deriv phi (r/R)) * xi (r/R^2)| +
      |r * phi (r/R) * ((r/R^2) * deriv xi (r/R^2))| := abs_add_le _ _
    _ ≤ C * bendingV R r + K * Real.sqrt (1+(bendingV R r)^2) := add_le_add hmain hcut
    _ ≤ (C+K) * Real.sqrt (1+(bendingV R r)^2) := by nlinarith

end
end CKSBending

end

end OAI
