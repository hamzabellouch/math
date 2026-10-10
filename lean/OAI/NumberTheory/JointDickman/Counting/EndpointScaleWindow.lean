import OAI.NumberTheory.JointDickman.Counting.CoefficientWindow

namespace OAI

/-! # The coefficient range for a fixed scaled endpoint support -/

namespace JointDickman
open Filter
open scoped Topology

theorem endpoint_scale_window {b : ℝ} (hb : 0 < b) :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X → Real.log X ≤ (5/2 : ℝ)*B →
      9 ≤ b*X ∧ (1/2 : ℝ)*B ≤ Real.log (b*X) ∧
        b*X ≤ Real.exp ((16/5 : ℝ)*B) := by
  have hlo : ∀ᶠ B : ℕ in atTop, -Real.log b ≤ (2/5 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2/5)).eventually_ge_atTop _
  have hhi : ∀ᶠ B : ℕ in atTop, Real.log b ≤ (7/10 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 7/10)).eventually_ge_atTop _
  filter_upwards [hlo,hhi,coefficient_support_window hb] with B hloB hhiB hw
  intro X hX hloglo hloghi
  have he : Real.log (b*X) = Real.log b+Real.log X := Real.log_mul hb.ne' hX.ne'
  refine ⟨(hw X hX hloglo).1,?_,?_⟩
  · rw [he]
    linarith
  · apply (Real.log_le_iff_le_exp (mul_pos hb hX)).mp
    rw [he]
    linarith

end JointDickman

end OAI
