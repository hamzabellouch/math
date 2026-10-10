import OAI.Geometry.SurfaceImmersion.Primitive.VelocityNormalGeometry

namespace OAI

/-! Normal-component bounds independent of the chosen angular derivative. -/
noncomputable section
open scoped Matrix BigOperators

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma unit_coordinate_abs_le {m : Vec} (hm : m ⬝ᵥ m = 1) (i : Fin 4) : |m i| ≤ 1 := by
  have hs : m i ^ 2 ≤ m ⬝ᵥ m := by
    simpa only [dotProduct, pow_two] using
      (Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) =>
        mul_self_nonneg (m j)) (Finset.mem_univ i))
  rw [hm] at hs
  exact (sq_le_one_iff_abs_le_one _).mp hs

lemma abs_dot_unit_le (W : Vec) {m : Vec} (hm : m ⬝ᵥ m = 1) :
    |W ⬝ᵥ m| ≤ 4 * ‖W‖ := by
  calc
    |W ⬝ᵥ m| ≤ ∑ i : Fin 4, |W i * m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4, |W i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (unit_coordinate_abs_le hm i)
    _ ≤ 4 * ‖W‖ := by
      simpa only [Real.norm_eq_abs, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using
        Pi.sum_norm_apply_le_norm W

theorem first_normal_bound {W m n : Vec} (hn : n ⬝ᵥ n = 1) (hmn : m ⬝ᵥ n = 0) (R d : ℝ) :
    |(W + (R * d) • m) ⬝ᵥ n| ≤ 4 * ‖W‖ := by
  rw [first_normal_derivative_independent hmn]
  exact abs_dot_unit_le W hn

theorem second_normal_error_bound {W m : Vec} (hm : m ⬝ᵥ m = 1) (R d : ℝ) :
    |(W + (R * d) • m) ⬝ᵥ m - R * d| ≤ 4 * ‖W‖ := by
  rw [second_normal_derivative hm]
  simpa only [add_sub_cancel_left] using abs_dot_unit_le W hm

/-- A fixed threshold is exceeded by a sufficiently large derivative at a turn. -/
theorem turn_dominates {r R B M T C d E : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hB : M + (T + C + 1) / r < B) (hd : B - M ≤ d) (hE : |E| ≤ C) :
    T + 1 < R * d + E := by
  have hdiv : (T + C + 1) / r < B - M := by linarith
  have hprod : T + C + 1 < r * (B - M) := by
    have hh := (div_lt_iff₀ hr).mp hdiv
    nlinarith
  have hBM : 0 < B - M := by nlinarith
  have hdpos : 0 < d := lt_of_lt_of_le hBM hd
  have hscale : r * d ≤ R * d := mul_le_mul_of_nonneg_right hR hdpos.le
  have hbase : r * (B - M) ≤ r * d := mul_le_mul_of_nonneg_left hd hr.le
  have hElow : -C ≤ E := (abs_le.mp hE).1
  linarith

end ClosedSurfaceR4.VelocityFrame

end

end OAI
