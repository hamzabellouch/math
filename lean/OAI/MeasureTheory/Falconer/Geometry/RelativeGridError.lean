import OAI.MeasureTheory.Falconer.Recursion.RoundedProfileError

namespace OAI

/-! Relative error bounds on the rounded intervals, uniform in their positions. -/
namespace Falconer
open Set

theorem innerProfileCell_relative_bounds {n : ℕ} (hn : 0 < n) {τ ε : ℝ}
    (_hτ : 0 < τ) (hε : 0 ≤ ε) (hmesh : 2/(n : ℝ) ≤ τ/2)
    (herror : 4/(n : ℝ) ≤ ε*(τ/2)) (c : ℝ × ℝ) (hc : τ ≤ c.2) :
    τ/2 ≤ (innerProfileCell n c).2 ∧ c.2 ≤ 2*(innerProfileCell n c).2 ∧
      ε*c.2+4/(n : ℝ) ≤ (3*ε)*(innerProfileCell n c).2 := by
  have hb := (innerProfileCell_length_bounds hn c).1
  have hmin : τ/2 ≤ (innerProfileCell n c).2 := by linarith
  have hhalf : c.2 ≤ 2*(innerProfileCell n c).2 := by linarith
  have hm1 := mul_le_mul_of_nonneg_left hhalf hε
  have hm2 := mul_le_mul_of_nonneg_left hmin hε
  exact ⟨hmin,hhalf,by nlinarith⟩

theorem rounded_profile_relative_linear {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hmesh : 2/(n : ℝ) ≤ τ/2) (herror : 4/(n : ℝ) ≤ ε*(τ/2))
    (c : ℝ × ℝ) (hc : τ ≤ c.2)
    (herr : ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ ε*c.2) :
    ∀ x ∈ Icc (innerProfileCell n c).1 ((innerProfileCell n c).1+(innerProfileCell n c).2),
      |intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x| ≤
        (3*ε)*(innerProfileCell n c).2 := by
  have hb := innerProfileCell_relative_bounds hn hτ hε hmesh herror c hc
  intro x hx
  exact (rounded_profile_linear_error hf hn c (hτ.trans_le hc)
    ((half_pos hτ).trans_le hb.1) herr hx).trans hb.2.2

theorem rounded_profile_relative_superlinear {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hmesh : 2/(n : ℝ) ≤ τ/2) (herror : 4/(n : ℝ) ≤ ε*(τ/2))
    (c : ℝ × ℝ) (hc : τ ≤ c.2)
    (herr : ∀ x ∈ Icc c.1 (c.1+c.2), -ε*c.2 ≤ intervalSecantError f c.1 c.2 x) :
    ∀ x ∈ Icc (innerProfileCell n c).1 ((innerProfileCell n c).1+(innerProfileCell n c).2),
      -(3*ε)*(innerProfileCell n c).2 ≤
        intervalSecantError f (innerProfileCell n c).1 (innerProfileCell n c).2 x := by
  have hb := innerProfileCell_relative_bounds hn hτ hε hmesh herror c hc
  intro x hx
  have he := rounded_profile_superlinear_error hf hn c (hτ.trans_le hc)
    ((half_pos hτ).trans_le hb.1) herr hx
  linarith [hb.2.2]

theorem rounded_profile_uniform_slope {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {n : ℕ} (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (hmesh : 2/(n : ℝ) ≤ τ/2)
    (c : ℝ × ℝ) (hc : τ ≤ c.2) :
    |intervalSecantSlope f (innerProfileCell n c).1 (innerProfileCell n c).2-
      intervalSecantSlope f c.1 c.2| ≤ 16/((n : ℝ)*τ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb := (innerProfileCell_length_bounds hn c).1
  have hd : τ/2 ≤ (innerProfileCell n c).2 := by linarith
  have he := rounded_profile_slope_error hf hn c (hτ.trans_le hc) ((half_pos hτ).trans_le hd)
  apply he.trans
  have hm := mul_le_mul_of_nonneg_left hd hnR.le
  have hr := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8)
    (mul_pos hnR (half_pos hτ)) hm
  exact hr.trans_eq (by ring)

end Falconer

end OAI
