import OAI.Probability.SLE.Geometry.PositiveRealDiskEstimate

namespace OAI

/-! A quantitative first-order kernel estimate for the inverted
positive-real function of a small slit. -/
noncomputable section
open Set Filter Function Metric Complex
open scoped Topology

namespace SLEExactGauge

lemma disk_kernel_remainder {v w : ℂ} {m : ℝ} (hm : 0<m) (hw : ‖w‖≤1/2)
    (hv : ‖v-(m:ℂ)‖≤4*m*‖w‖) :
    ‖w*v/(1-w^2)-(m:ℂ)*w‖≤10*m*‖w‖^2 := by
  have hr : 0≤‖w‖ := norm_nonneg _
  have hr1 : ‖w‖≤1 := by linarith
  have hd : 1/2≤‖(1:ℂ)-w^2‖ := by
    have hn := norm_sub_norm_le (1:ℂ) (w^2)
    rw [norm_one,norm_pow] at hn
    nlinarith
  have hdp : 0<‖(1:ℂ)-w^2‖ := by linarith
  have hd0 : (1:ℂ)-w^2≠0 := norm_pos_iff.mp hdp
  have he : w*v/(1-w^2)-(m:ℂ)*w=
      w*((v-(m:ℂ))+(m:ℂ)*w^2)/(1-w^2) := by
    field_simp [hd0]
    ring
  have hv' : ‖(v-(m:ℂ))+(m:ℂ)*w^2‖≤5*m*‖w‖ := by
    calc
      ‖(v-(m:ℂ))+(m:ℂ)*w^2‖ ≤ ‖v-(m:ℂ)‖+‖(m:ℂ)*w^2‖ := norm_add_le _ _
      _ ≤ 4*m*‖w‖+m*‖w‖^2 := by
        rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hm]
        exact add_le_add hv le_rfl
      _ ≤ 5*m*‖w‖ := by nlinarith [mul_nonneg hm.le (mul_nonneg hr (sub_nonneg.mpr hr1))]
  rw [he,norm_div,norm_mul]
  calc
    ‖w‖*‖(v-(m:ℂ))+(m:ℂ)*w^2‖/‖(1:ℂ)-w^2‖ ≤
        ‖w‖*(5*m*‖w‖)/‖(1:ℂ)-w^2‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv' hr) hdp.le
    _ ≤ ‖w‖*(5*m*‖w‖)/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
    _ = 10*m*‖w‖^2 := by ring

theorem positive_real_disk_kernel_remainder {H : ℂ → ℂ} {m : ℝ} (hm : 0<m)
    (hH : DifferentiableOn ℂ H (ball 0 1)) (h0 : H 0=(m:ℂ))
    (hpos : ∀ z∈ball (0:ℂ) 1, 0≤(H z).re)
    {w : ℂ} (hw : ‖w‖≤1/2) :
    ‖w*H w/(1-w^2)-(m:ℂ)*w‖≤10*m*‖w‖^2 := by
  apply disk_kernel_remainder hm hw
  have hr : ‖w‖<1 := by linarith
  have hb := positive_real_disk_deviation hm hH h0 hpos (mem_ball_zero_iff.mpr hr)
  apply hb.trans
  apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
  nlinarith [norm_nonneg w, mul_nonneg hm.le (norm_nonneg w)]

end SLEExactGauge

end

end OAI
