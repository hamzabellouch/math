import OAI.Probability.FreeIsing.Estimates.MessageFunction
import OAI.Probability.FreeIsing.Gaussian.BinaryFusion

namespace OAI

noncomputable section

namespace Problem367

theorem tanh_add_eq_binaryFusion (a b : ℝ) :
    Real.tanh (a + b) = binaryFusion (Real.tanh a) (Real.tanh b) := by
  have ha : |Real.tanh a| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (Real.tanh_sq_lt_one a)
  have hb : |Real.tanh b| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (Real.tanh_sq_lt_one b)
  apply (eq_div_iff (binaryFusion_denominator_pos ha hb).ne').2
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp
  have hc : Real.cosh b * Real.cosh a + Real.sinh a * Real.sinh b ≠ 0 := by
    simpa only [Real.cosh_add, mul_comm] using (Real.cosh_pos (a + b)).ne'
  exact mul_div_cancel_right₀ _ hc

theorem artanh_binaryFusion {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    Real.artanh (binaryFusion x y) = Real.artanh x + Real.artanh y := by
  apply Real.tanh_injective
  rw [Real.tanh_artanh (abs_lt.mp (abs_binaryFusion_lt_one hx hy)),
    tanh_add_eq_binaryFusion, Real.tanh_artanh (abs_lt.mp hx),
    Real.tanh_artanh (abs_lt.mp hy)]

theorem artanh_binaryFusion_scaled {theta x y : ℝ}
    (hθ : |theta| < 1) (hx : |x| < 1) (hy : |y| < 1) :
    Real.artanh ((x + theta * y) / (1 + theta * x * y)) =
      Real.artanh x + cavityMessage theta (Real.artanh y) := by
  have hprod : |theta * y| < 1 := binaryFusion_abs_mul_lt_one hθ hy
  have h := artanh_binaryFusion hx hprod
  simpa only [binaryFusion, cavityMessage, Real.tanh_artanh (abs_lt.mp hy),
    mul_left_comm, mul_assoc] using h

theorem artanh_binaryFusion_scaled_of_mem {theta x y : ℝ}
    (hθ : theta ∈ Set.Ioo (-1 : ℝ) 1)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.artanh ((x + theta * y) / (1 + theta * x * y)) =
      Real.artanh x + cavityMessage theta (Real.artanh y) :=
  artanh_binaryFusion_scaled (abs_lt.mpr hθ) (abs_lt.mpr hx) (abs_lt.mpr hy)

end Problem367

end

end OAI
