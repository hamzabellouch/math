import OAI.NumberTheory.Ostmann.Quadratic.QuadraticLogDerivative

namespace OAI

/-! # Uniform Schwartz decay on the compact logarithmic window -/

namespace Ostmann

open MeasureTheory
open scoped SchwartzMap

noncomputable def quadraticLogDecayConstant (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) : ℝ :=
  Real.exp 3 ^ A * SchwartzMap.seminorm ℝ A 0 ρ

 theorem quadraticLogDecayConstant_nonneg (ρ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    0 ≤ quadraticLogDecayConstant ρ A := by
  unfold quadraticLogDecayConstant
  positivity

 theorem quadratic_log_value_decay (ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    {X u : ℝ} (hX : 0 < X) (hu : u ≤ 3) :
    ‖ρ (X * Real.exp (-u))‖ ≤ quadraticLogDecayConstant ρ A / X ^ A := by
  have hy : 0 < X * Real.exp (-u) := mul_pos hX (Real.exp_pos _)
  have hs := SchwartzMap.norm_pow_mul_le_seminorm ℝ ρ A (X * Real.exp (-u))
  rw [Real.norm_eq_abs, abs_of_pos hy] at hs
  have he : X = (X * Real.exp (-u)) * Real.exp u := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  apply (le_div_iff₀ (pow_pos hX A)).mpr
  calc
    _ = Real.exp u ^ A * ((X * Real.exp (-u)) ^ A * ‖ρ (X * Real.exp (-u))‖) := by
      calc
        _ = ‖ρ (X * Real.exp (-u))‖ * ((X * Real.exp (-u)) * Real.exp u) ^ A :=
          congrArg (fun z : ℝ => ‖ρ (X * Real.exp (-u))‖ * z ^ A) he
        _ = _ := by rw [mul_pow]; ring
    _ ≤ Real.exp 3 ^ A * SchwartzMap.seminorm ℝ A 0 ρ := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Real.exp_nonneg _) (Real.exp_le_exp.mpr hu) A
      · exact hs
      · positivity
      · positivity
    _ = _ := rfl

 theorem quadratic_log_product_decay (B ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    (hB : tsupport B ⊆ Set.Icc (-3 : ℝ) 3) {X : ℝ} (hX : 0 < X) (u : ℝ) :
    ‖B u * ρ (X * Real.exp (-u))‖ ≤
      (quadraticLogDecayConstant ρ A / X ^ A) * ‖B u‖ := by
  by_cases hb : B u = 0
  · simp [hb]
  · have hu : u ∈ tsupport B := subset_tsupport B hb
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (quadratic_log_value_decay ρ A hX (hB hu).2) (norm_nonneg _)

 theorem quadratic_log_product_integral (B ρ : 𝓢(ℝ, ℂ)) (A : ℕ)
    (hB : tsupport B ⊆ Set.Icc (-3 : ℝ) 3) {X : ℝ} (hX : 0 < X) :
    (∫ u : ℝ, ‖B u * ρ (X * Real.exp (-u))‖) ≤
      (quadraticLogDecayConstant ρ A / X ^ A) * ∫ u : ℝ, ‖B u‖ := by
  calc
    _ ≤ ∫ u : ℝ, (quadraticLogDecayConstant ρ A / X ^ A) * ‖B u‖ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        (B.integrable.norm.const_mul _) (Filter.Eventually.of_forall
          (quadratic_log_product_decay B ρ A hB hX))
    _ = _ := integral_const_mul _ _

 theorem quadraticSmoothLogCutoff_support :
    tsupport quadraticSmoothLogCutoff ⊆ Set.Icc (-3 : ℝ) 3 := by
  intro u hu
  have hs : tsupport quadraticSmoothLogCutoff ⊆ tsupport quadraticLogBump :=
    tsupport_comp_subset (g := Complex.ofReal) (by simp) quadraticLogBump
  have hh := hs hu
  rw [quadraticLogBump.tsupport_eq] at hh
  have ha : |u| ≤ 3 := by
    simpa only [quadraticLogBump, Metric.mem_closedBall, Real.dist_eq, sub_zero] using hh
  exact abs_le.mp ha

 theorem quadraticSmoothLogCutoff_deriv_support :
    tsupport (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff) ⊆
      Set.Icc (-3 : ℝ) 3 :=
  (SchwartzMap.tsupport_derivCLM_subset ℂ quadraticSmoothLogCutoff).trans
    quadraticSmoothLogCutoff_support

 theorem quadraticSmoothLogCutoff_second_support :
    tsupport (SchwartzMap.derivCLM ℂ ℂ
      (SchwartzMap.derivCLM ℂ ℂ quadraticSmoothLogCutoff)) ⊆ Set.Icc (-3 : ℝ) 3 :=
  (SchwartzMap.tsupport_derivCLM_subset ℂ _).trans
    quadraticSmoothLogCutoff_deriv_support

end Ostmann

end OAI
