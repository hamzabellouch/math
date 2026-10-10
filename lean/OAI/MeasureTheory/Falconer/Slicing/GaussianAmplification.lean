import OAI.MeasureTheory.Falconer.Slicing.GaussianDamping

namespace OAI

/-! # Undoing Gaussian damping on a bounded original probability -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

noncomputable def gaussianAmplifiedMeasure (μ : Measure (Space d)) : Measure (Space d) :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp ((Real.pi^2/2)*‖x‖^2)))

theorem gaussianAmplifiedMeasure_le (μ : Measure (Space d)) {D : ℝ} (hD : 0 ≤ D)
    (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D) :
    gaussianAmplifiedMeasure μ ≤ ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2)) • μ := by
  calc
    _ ≤ μ.withDensity (fun _ => ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2))) := by
      apply withDensity_mono
      filter_upwards [hsupport] with x hx
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hD).mpr hx) (by positivity)
    _ = _ := withDensity_const _

theorem gaussianAmplifiedMeasure_finite (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {D : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D) :
    IsFiniteMeasure (gaussianAmplifiedMeasure μ) := by
  constructor
  apply ((gaussianAmplifiedMeasure_le μ hD hsupport) univ).trans_lt
  change ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2))*μ univ < ∞
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)

theorem gaussianDampedMeasure_amplified (μ : Measure (Space d)) :
    gaussianDampedMeasure (gaussianAmplifiedMeasure μ) = μ := by
  rw [gaussianDampedMeasure,gaussianAmplifiedMeasure,← withDensity_mul μ (by fun_prop) (by fun_prop)]
  have he : (fun x : Space d => ENNReal.ofReal (Real.exp ((Real.pi^2/2)*‖x‖^2))) *
      (fun x => ENNReal.ofReal (Real.exp (-(Real.pi^2/2)*‖x‖^2))) = fun _ => (1:ℝ≥0∞) := by
    funext x
    dsimp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    have hz : (Real.pi^2/2)*‖x‖^2+(-(Real.pi^2/2))*‖x‖^2 = 0 := by ring
    rw [hz,Real.exp_zero,ENNReal.ofReal_one]
  rw [he,withDensity_const,one_smul]

theorem gaussianAmplifiedMeasure_ball_bound (μ : Measure (Space d))
    {D δ K s : ℝ} (hD : 0 ≤ D) (hsupport : ∀ᵐ x ∂μ, ‖x‖ ≤ D)
    (hb : ∀ x : Space d, ∀ r : ℝ, δ ≤ r →
      μ (ball x r) ≤ ENNReal.ofReal (K*r^s)) :
    ∀ x : Space d, ∀ r : ℝ, δ ≤ r →
      gaussianAmplifiedMeasure μ (ball x r) ≤
        ENNReal.ofReal ((Real.exp ((Real.pi^2/2)*D^2)*K)*r^s) := by
  intro x r hr
  calc
    _ ≤ (ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2)) • μ) (ball x r) :=
      (gaussianAmplifiedMeasure_le μ hD hsupport) _
    _ = ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2))*μ (ball x r) := by rfl
    _ ≤ ENNReal.ofReal (Real.exp ((Real.pi^2/2)*D^2))*ENNReal.ofReal (K*r^s) :=
      mul_le_mul_right (hb x r hr) _
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]; congr 1; ring

end Falconer

end OAI
