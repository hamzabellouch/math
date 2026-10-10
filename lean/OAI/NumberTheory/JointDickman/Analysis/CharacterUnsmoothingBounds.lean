import OAI.NumberTheory.JointDickman.Analysis.CharacterRieszDifference
import OAI.NumberTheory.JointDickman.Analysis.CharacterRieszLogBound

namespace OAI

/-! # Uniform primitive bounds and an elementary complex unsmoothing inequality -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem complex_norm_of_riesz_difference {A U V : ℂ} {h : ℝ} (hh : 0 < h)
    (he : ‖U-V-(h:ℂ)*A‖ ≤ h*(h+1)) :
    ‖A‖ ≤ h+1+(‖U‖+‖V‖)/h := by
  have hid : (U-V)-(U-V-(h:ℂ)*A) = (h:ℂ)*A := by ring
  have ht := norm_sub_le (U-V) (U-V-(h:ℂ)*A)
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh] at ht
  have huv := norm_sub_le U V
  have hb : ‖A‖*h ≤ ‖U‖+‖V‖+h*(h+1) := by linarith
  calc
    _ ≤ (‖U‖+‖V‖+h*(h+1))/h := (le_div_iff₀ hh).mpr hb
    _ = _ := by field_simp; ring

theorem squarefreeCharacterPrimitive_uniform_bound {z C H : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ (Real.log x)^C → χ ≠ 1 →
        ∀ y : ℝ, x ≤ y → y ≤ 2*x →
        ‖squarefreeCharacterPrimitive χ z y‖ ≤ K*x^2*(Real.log x)^(-H) := by
  obtain ⟨K,hK,hR⟩ := squarefreeCharacterRiesz_log_bound hz hz1 hC hH
  obtain ⟨X,hX⟩ := eventually_atTop.mp hR
  refine ⟨4*K, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max X 3)] with x hx
  intro q _ χ hq hn y hxy hyx
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hq' : (q:ℝ) ≤ (Real.log y)^C := hq.trans
    (Real.rpow_le_rpow hlogx.le hlog hC)
  have hb := hX y (hxX.trans hxy) q χ hq' hn
  have hp : (Real.log y)^(-H) ≤ (Real.log x)^(-H) :=
    Real.rpow_le_rpow_of_nonpos hlogx hlog (by linarith)
  have hy2 : y^2 ≤ 4*x^2 := by nlinarith
  rw [squarefreeCharacterPrimitive, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
  calc
    _ ≤ y*(K*y*(Real.log y)^(-H)) := mul_le_mul_of_nonneg_left hb hy0.le
    _ = K*y^2*(Real.log y)^(-H) := by ring
    _ ≤ K*y^2*(Real.log x)^(-H) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ K*(4*x^2)*(Real.log x)^(-H) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hy2 hK.le) (Real.rpow_nonneg hlogx.le _)
    _ = _ := by ring

end JointDickman

end OAI
