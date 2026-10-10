import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetLinear
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetConvolution

namespace OAI

/-! Bounded differentiation and linear maps commute with spatial convolution. -/

noncomputable section
namespace ForcedComputation.BoundedSpatialJets

open MeasureTheory
open scoped Topology ContDiff

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Linear
variable (G : Type*) [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Fixed linear postcomposition commutes with convolution on each finite jet space. -/
theorem postcomposeCLM_convolution (k : ℕ) (L : F →L[ℝ] G)
    (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ) (J : Space E F k) :
    postcomposeCLM E F G k L (convolution E F k μ w hw J) =
      convolution E G k μ w hw (postcomposeCLM E F G k L J) := by
  apply function_injective E G k
  ext x
  simp only [postcomposeCLM_apply, function_postcompose, function_convolution]
  have hi := BoundedKernel.integrand_integrable E F μ w (function E F k J)
    hw (function E F k J).continuous ‖J‖ (norm_function_le E F k J) x
  simpa only [map_smul] using (L.integral_comp_comm hi).symm

end Linear

/-- A bounded spatial derivative may be taken on the input of a convolution. -/
theorem derivativeCLM_convolution (k : ℕ)
    (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ) (J : Space E F (k+1)) :
    derivativeCLM E F k (convolution E F (k+1) μ w hw J) =
      convolution E (E →L[ℝ] F) k μ w hw (derivativeCLM E F k J) := by
  apply function_injective E (E →L[ℝ] F) k
  apply BoundedContinuousFunction.ext
  intro x
  change function E (E →L[ℝ] F) k (derivative E F k (convolution E F (k+1) μ w hw J)) x = _
  rw [function_derivative, function_convolution]
  have he : (function E F (k+1) (convolution E F (k+1) μ w hw J) : E → F) =
      BoundedKernel.convolve E F μ w (function E F (k+1) J) := by
    funext z
    exact function_convolution E F (k+1) μ w hw J z
  rw [he]
  have hd : ∀ z, ‖fderiv ℝ (function E F (k+1) J) z‖ ≤ ‖J‖ := by
    intro z
    rw [← function_derivative E F k J z]
    exact (norm_function_le E (E →L[ℝ] F) k (derivative E F k J) z).trans
      (norm_derivative_le E F k J)
  have hp := BoundedKernel.fderiv_convolve E F μ w (function E F (k+1) J) hw
    ((function_contDiff E F (k+1) J).of_le (by simp))
    ‖J‖ ‖J‖ (norm_function_le E F (k+1) J) hd x
  exact hp.trans (integral_congr_ae (ae_of_all _ (fun y => by
    change w y • fderiv ℝ (function E F (k+1) J) (x-y) =
      w y • function E (E →L[ℝ] F) k (derivative E F k J) (x-y)
    rw [function_derivative])))

/-- In particular, directional derivatives commute with spatial convolution. -/
theorem directionalDerivativeCLM_convolution (k : ℕ) (v : E)
    (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ) (J : Space E F (k+1)) :
    directionalDerivativeCLM E F k v (convolution E F (k+1) μ w hw J) =
      convolution E F k μ w hw (directionalDerivativeCLM E F k v J) := by
  change postcomposeCLM E (E →L[ℝ] F) F k (ContinuousLinearMap.apply ℝ F v)
    (derivativeCLM E F k (convolution E F (k+1) μ w hw J)) = _
  exact (congrArg (postcomposeCLM E (E →L[ℝ] F) F k (ContinuousLinearMap.apply ℝ F v))
    (derivativeCLM_convolution E F k μ w hw J)).trans
      (postcomposeCLM_convolution E (E →L[ℝ] F) F k (ContinuousLinearMap.apply ℝ F v)
        μ w hw (derivativeCLM E F k J))

end ForcedComputation.BoundedSpatialJets

end

end OAI
