import OAI.NumberTheory.JointDickman.Analysis.CharacterUniformSublog

namespace OAI

/-! # The qualitative character-distance divergence needed by the application

This is weaker than the quantitative KMT input. Its proof uses the Euler
comparison, finite differencing of logarithmic phases and partial summation.
-/
namespace JointDickman
open Complex Filter PublishedInputs
open scoped Topology

/-- Qualitative uniform divergence of the nonprincipal-character distance
on the entire frequency interval. -/
theorem characterDistanceDivergence : CharacterDistanceDivergence := by
  intro q _ χ hχ R
  obtain ⟨C,hC⟩ := characterDistance_ge_log_sub_L
  let η := Real.exp (-(R+C+1))
  have hη : 0 < η := Real.exp_pos _
  filter_upwards [character_LFunction_uniform_sublog χ hχ hη,
    eventually_ge_atTop (max 2 (Real.exp 1))] with X hbound hX
  intro t ht
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hXe
  have hlog : 0 < Real.log X := by linarith
  have hs : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
    linarith [one_div_pos.mpr hlog]
  have hn : 0 < ‖χ.LFunction (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ := by
    apply norm_pos_iff.mpr
    rw [χ.LFunction_eq_LSeries hs]
    exact χ.LSeries_ne_zero_of_one_lt_re hs
  have hl := Real.log_le_log hn (hbound t ht)
  rw [Real.log_mul hη.ne' hlog.ne'] at hl
  dsimp only [η] at hl
  rw [Real.log_exp] at hl
  have hd := hC q χ X hX t
  linarith


end JointDickman

end OAI
