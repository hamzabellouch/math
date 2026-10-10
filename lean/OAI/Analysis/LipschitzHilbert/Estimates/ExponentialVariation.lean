import OAI.Analysis.LipschitzHilbert.Trees.HierarchyVariation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! Variation of exponential weights from variation of their logarithms. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem norm_exp_sub_le_of_re_le (a b : ℂ) (C : ℝ) (ha : a.re ≤ C) (hb : b.re ≤ C) :
    ‖Complex.exp b - Complex.exp a‖ ≤ Real.exp C * ‖b - a‖ := by
  have hconvex : Convex ℝ {z : ℂ | z.re ≤ C} := by
    intro x hx y hy u v hu hv huv
    change (u • x + v • y).re ≤ C
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    change x.re ≤ C at hx
    change y.re ≤ C at hy
    have huC := mul_le_mul_of_nonneg_left hx hu
    have hvC := mul_le_mul_of_nonneg_left hy hv
    have htotal : u * C + v * C = C := by rw [← add_mul, huv, one_mul]
    linarith
  apply hconvex.norm_image_sub_le_of_norm_deriv_le
    (fun z _ => Complex.differentiableAt_exp) _ ha hb
  intro z hz
  rw [Complex.deriv_exp, Complex.norm_exp]
  exact Real.exp_le_exp.mpr hz

theorem exponential_sequence_variation (L : ℕ → ℂ) (N : ℕ) (C : ℝ)
    (hL : ∀ j ≤ N, (L j).re ≤ C) :
    ‖Complex.exp (L N)‖ +
      (∑ j ∈ Finset.range N, ‖Complex.exp (L (j + 1)) - Complex.exp (L j)‖) ≤
      Real.exp C * (1 + ∑ j ∈ Finset.range N, ‖L (j + 1) - L j‖) := by
  have hend : ‖Complex.exp (L N)‖ ≤ Real.exp C := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hL N le_rfl)
  have hsum : (∑ j ∈ Finset.range N, ‖Complex.exp (L (j + 1)) - Complex.exp (L j)‖) ≤
      Real.exp C * ∑ j ∈ Finset.range N, ‖L (j + 1) - L j‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjN := Finset.mem_range.mp hj
    exact norm_exp_sub_le_of_re_le (L j) (L (j + 1)) C
      (hL j (by omega)) (hL (j + 1) (by omega))
  nlinarith

theorem logarithm_increment_bound (a P R : ℝ) (z : ℂ)
    (ha : 0 ≤ a) (hP : 0 ≤ P) (hR : 0 ≤ R) :
    ‖((a * P : ℝ) : ℂ) - z * (R : ℂ)‖ ≤ a * P + ‖z‖ * R := by
  calc
    _ ≤ ‖((a * P : ℝ) : ℂ)‖ + ‖z * (R : ℂ)‖ := norm_sub_le _ _
    _ = _ := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ha hP),
        abs_of_nonneg hR]

theorem exponential_hierarchy_variation (L : ℕ → ℂ) (n R : ℕ → ℝ)
    (z : ℕ → ℂ) (N K : ℕ) (a C Z : ℝ)
    (hn : ∀ j ≤ N, 0 < n j) (hmono : AntitoneOn n (Set.Iic N))
    (hR0 : ∀ j < N, 0 ≤ R j)
    (hR : ∀ i < N, R i ≤ Real.log (n (i + 1 - K) / n (i + 1)))
    (ha : 0 ≤ a) (hZ : 0 ≤ Z) (hz : ∀ j < N, ‖z j‖ ≤ Z)
    (hL : ∀ j ≤ N, (L j).re ≤ C)
    (hincr : ∀ j < N, L (j + 1) - L j =
      ((a * Real.log (n j / n (j + 1)) : ℝ) : ℂ) - z j * (R j : ℂ)) :
    ‖Complex.exp (L N)‖ +
      (∑ j ∈ Finset.range N, ‖Complex.exp (L (j + 1)) - Complex.exp (L j)‖) ≤
      Real.exp C * (1 + (a + Z * K) * Real.log (n 0 / n N)) := by
  have hP (j : ℕ) (hj : j < N) : 0 ≤ Real.log (n j / n (j + 1)) := by
    apply Real.log_nonneg
    exact (one_le_div (hn (j + 1) (by omega))).2
      (hmono (by change j ≤ N; omega) (by change j + 1 ≤ N; omega) (by omega))
  have hsum : (∑ j ∈ Finset.range N, ‖L (j + 1) - L j‖) ≤
      (a + Z * K) * Real.log (n 0 / n N) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, (a * Real.log (n j / n (j + 1)) + Z * R j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN := Finset.mem_range.mp hj
        rw [hincr j hjN]
        exact (logarithm_increment_bound a _ _ _ ha (hP j hjN) (hR0 j hjN)).trans
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hz j hjN) (hR0 j hjN)))
      _ = a * Real.log (n 0 / n N) + Z * ∑ j ∈ Finset.range N, R j := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_log_ratios n N hn]
      _ ≤ a * Real.log (n 0 / n N) + Z * ((K : ℝ) * Real.log (n 0 / n N)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (full_root_log_variation n R N K hn hmono hR) hZ)
      _ = _ := by ring
  exact (exponential_sequence_variation L N C hL).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) (Real.exp_pos C).le)

end LipschitzHilbert

end

end OAI
