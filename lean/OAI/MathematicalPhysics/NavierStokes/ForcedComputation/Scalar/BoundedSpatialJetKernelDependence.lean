import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetConvolution
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetBilinear

namespace OAI

/-! Dependence of finite-jet convolution operators on their integrable scalar kernels. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem convolutionCLM_sub_kernel (k : ℕ) (μ : Measure E) (w v : E → ℝ)
    (hw : Integrable w μ) (hv : Integrable v μ) :
    convolutionCLM E F k μ (w - v) (hw.sub hv) =
      convolutionCLM E F k μ w hw - convolutionCLM E F k μ v hv := by
  apply ContinuousLinearMap.ext
  intro J
  apply Subtype.ext
  funext i
  apply BoundedContinuousFunction.ext
  intro x
  change (∫ y, (w y - v y) • J.val i (x - y) ∂μ) =
    (∫ y, w y • J.val i (x - y) ∂μ) - ∫ y, v y • J.val i (x - y) ∂μ
  simp_rw [sub_smul]
  exact integral_sub
    (BoundedKernel.integrand_integrable E (Value E F i.val) μ w (J.val i)
      hw (J.val i).continuous ‖J‖ (norm_jet_le E F k J i) x)
    (BoundedKernel.integrand_integrable E (Value E F i.val) μ v (J.val i)
      hv (J.val i).continuous ‖J‖ (norm_jet_le E F k J i) x)

/-- L1 perturbations of the scalar kernel uniformly control the whole jet operator. -/
theorem norm_convolutionCLM_sub_le (k : ℕ) (μ : Measure E) (w v : E → ℝ)
    (hw : Integrable w μ) (hv : Integrable v μ) :
    ‖convolutionCLM E F k μ w hw - convolutionCLM E F k μ v hv‖ ≤
      ∫ y, |w y - v y| ∂μ := by
  rw [← convolutionCLM_sub_kernel E F k μ w v hw hv]
  exact norm_convolutionCLM_le E F k μ (w - v) (hw.sub hv)

/-- The convolution operator in the fixed normed operator space. -/
def convolutionOperator (k : ℕ) (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ) :
    Operator E F F k := convolutionCLM E F k μ w hw

@[simp] theorem operatorEquiv_convolutionOperator (k : ℕ) (μ : Measure E)
    (w : E → ℝ) (hw : Integrable w μ) :
    operatorEquiv E F F k (convolutionOperator E F k μ w hw) =
      convolutionCLM E F k μ w hw := rfl

/-- L1 convergence of kernels implies convergence in operator norm at every finite jet order. -/
theorem tendsto_convolutionCLM {A : Type*} (l : Filter A) (k : ℕ) (μ : Measure E)
    (w : A → E → ℝ) (v : E → ℝ) (hw : ∀ a, Integrable (w a) μ)
    (hv : Integrable v μ)
    (h : Tendsto (fun a => ∫ y, |w a y - v y| ∂μ) l (𝓝 0)) :
    Tendsto (fun a => convolutionCLM E F k μ (w a) (hw a)) l
      (𝓝 (convolutionCLM E F k μ v hv)) := by
  have hnorm : Tendsto
      (fun a => ‖convolutionOperator E F k μ (w a) (hw a) -
        convolutionOperator E F k μ v hv‖) l (𝓝 0) := by
    apply squeeze_zero (fun a => norm_nonneg _)
    · intro a
      exact norm_convolutionCLM_sub_le E F k μ (w a) v (hw a) hv
    · exact h
  have ht : Tendsto (fun a => convolutionOperator E F k μ (w a) (hw a)) l
      (𝓝 (convolutionOperator E F k μ v hv)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have he := ((operatorEquiv E F F k).continuous.tendsto
    (convolutionOperator E F k μ v hv)).comp ht
  simpa only [Function.comp_def, operatorEquiv_convolutionOperator] using he

/-- Forgetting higher derivatives commutes exactly with convolution. -/
theorem convolution_truncate (k n : ℕ) (hkn : k ≤ n) (μ : Measure E)
    (w : E → ℝ) (hw : Integrable w μ) (J : Space E F n) :
    convolution E F k μ w hw (truncate E F k n hkn J) =
      truncate E F k n hkn (convolution E F n μ w hw J) := by
  apply function_injective E F k
  apply BoundedContinuousFunction.ext
  intro x
  simp only [function_convolution, function_truncate]

/-- The exact operator identity used when comparing fixed points at different jet orders. -/
theorem convolutionCLM_truncate (k n : ℕ) (hkn : k ≤ n) (μ : Measure E)
    (w : E → ℝ) (hw : Integrable w μ) :
    (convolutionCLM E F k μ w hw).comp (truncateCLM E F k n hkn) =
      (truncateCLM E F k n hkn).comp (convolutionCLM E F n μ w hw) := by
  apply ContinuousLinearMap.ext
  intro J
  exact convolution_truncate E F k n hkn μ w hw J

end ForcedComputation.BoundedSpatialJets

end

end OAI
