import OAI.Analysis.KadisonKastler.GaussianStateDerivative

namespace OAI

/-! # Gaussian averaging of a strongly holomorphic moving input -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_moving_differentiableAt
    (B B' : ℂ → H →L[ℂ] H)
    (hd : ∀ w x, HasDerivAt (fun v => B v x) (B' w x) w)
    (r : ℝ) (hr : 0 < r) (z : ℂ) (x : H)
    (C₀ C₁ : ℝ)
    (hb₀ : ∀ w ∈ Metric.ball z 1, ‖B w‖ ≤ C₀)
    (hb₁ : ∀ w ∈ Metric.ball z 1, ‖B' w‖ ≤ C₁) :
    DifferentiableAt ℂ (fun w => gaussianStateAverage U hU (B w) r hr w x) z := by
  let R := ‖z‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hwR {w : ℂ} (hw : w ∈ Metric.ball z 1) : ‖w‖ ≤ R := by
    have hi : ‖w‖ ≤ ‖z‖ + dist w z := by
      calc
        _ = ‖z + (w - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ = _ := by rw [dist_eq_norm]
    have hw' : dist w z < 1 := hw
    dsimp [R]
    linarith
  let F : ℂ → ℝ → H := fun w t => gaussianStateKernel r w t • stateActionOrbit U (B w) t x
  let F' : ℂ → ℝ → H := fun w t =>
    gaussianStateKernel r w t • stateActionOrbit U (B' w) t x +
      gaussianStateKernelDeriv r w t • stateActionOrbit U (B w) t x
  have hF (w : ℂ) : AEStronglyMeasurable (F w) := by
    have hc : Continuous (gaussianStateKernel r w) := by unfold gaussianStateKernel; fun_prop
    exact hc.aestronglyMeasurable.smul (stateActionOrbit_continuous U hU (B w) x).aestronglyMeasurable
  have hF' : AEStronglyMeasurable (F' z) := by
    have hc : Continuous (gaussianStateKernel r z) := by unfold gaussianStateKernel; fun_prop
    have hd' : Continuous (gaussianStateKernelDeriv r z) := by
      unfold gaussianStateKernelDeriv gaussianStateKernel; fun_prop
    exact (hc.aestronglyMeasurable.smul
      (stateActionOrbit_continuous U hU (B' z) x).aestronglyMeasurable).add
      (hd'.aestronglyMeasurable.smul
      (stateActionOrbit_continuous U hU (B z) x).aestronglyMeasurable)
  have hFD : ∀ᵐ t : ℝ, ∀ w ∈ Metric.ball z 1, HasDerivAt (fun v => F v t) (F' w t) w := by
    filter_upwards [] with t w _
    let u := U (Multiplicative.ofAdd t)
    have hv := (u : H →L[ℂ] H).hasFDerivAt.comp_hasDerivAt w
      (hd w (star (u : H →L[ℂ] H) x))
    exact (gaussianStateKernel_hasDerivAt r t w).smul hv
  let E₀ : ℝ → ℝ := fun t => Real.exp (2 * r * R ^ 2) * Real.exp (-(r / 2) * t ^ 2)
  let E₁ : ℝ → ℝ := gaussianDerivativeEnvelope r R
  have hE₀ : Integrable E₀ := (integrable_exp_neg_mul_sq (by positivity : 0 < r / 2)).const_mul _
  have hE₁ : Integrable E₁ := gaussianDerivativeEnvelope_integrable hr R
  have hbound : ∀ᵐ t : ℝ, ∀ w ∈ Metric.ball z 1,
      ‖F' w t‖ ≤ (E₀ t * C₁ + E₁ t * C₀) * ‖x‖ := by
    filter_upwards [] with t w hw
    have hk := gaussianStateKernel_local_bound hr hR (hwR hw) t
    have hk' := gaussianStateKernelDeriv_local_bound hr hR (hwR hw) t
    have hv₀ : ‖stateActionOrbit U (B w) t x‖ ≤ C₀ * ‖x‖ := by
      apply ((stateActionOrbit U (B w) t).le_opNorm x).trans
      rw [stateActionOrbit_norm]
      exact mul_le_mul_of_nonneg_right (hb₀ w hw) (norm_nonneg x)
    have hv₁ : ‖stateActionOrbit U (B' w) t x‖ ≤ C₁ * ‖x‖ := by
      apply ((stateActionOrbit U (B' w) t).le_opNorm x).trans
      rw [stateActionOrbit_norm]
      exact mul_le_mul_of_nonneg_right (hb₁ w hw) (norm_nonneg x)
    calc
      ‖F' w t‖ ≤ ‖gaussianStateKernel r w t‖ * ‖stateActionOrbit U (B' w) t x‖ +
          ‖gaussianStateKernelDeriv r w t‖ * ‖stateActionOrbit U (B w) t x‖ := by
        simpa only [norm_smul] using norm_add_le
          (gaussianStateKernel r w t • stateActionOrbit U (B' w) t x)
          (gaussianStateKernelDeriv r w t • stateActionOrbit U (B w) t x)
      _ ≤ E₀ t * (C₁ * ‖x‖) + E₁ t * (C₀ * ‖x‖) :=
        add_le_add (mul_le_mul hk hv₁ (norm_nonneg _) (by dsimp [E₀]; positivity))
          (mul_le_mul hk' hv₀ (norm_nonneg _) (by dsimp [E₁, gaussianDerivativeEnvelope]; positivity))
      _ = _ := by ring
  have hi := gaussianVector_integrable (fun t => stateActionOrbit U (B z) t x)
    (stateActionOrbit_continuous U hU (B z) x) (‖B z‖ * ‖x‖)
    (fun t => ((stateActionOrbit U (B z) t).le_opNorm x).trans_eq (by rw [stateActionOrbit_norm])) r hr z
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z zero_lt_one) (Eventually.of_forall hF) hi hF' hbound
    (((hE₀.mul_const C₁).add (hE₁.mul_const C₀)).mul_const ‖x‖) hFD).2.differentiableAt

end

end KadisonKastler

end OAI
