import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneHeatKernel
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetConvolution

namespace OAI

/-! The normalized Gaussian and its first spatial derivatives act on every finite jet space. -/

noncomputable section
namespace ForcedComputation.PlaneHeat

open MeasureTheory ShearFlows
open scoped Topology

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The Gaussian heat operator on bounded spatial jets of order `k`. -/
def heatOperator (k : ℕ) (t : ℝ) (ht : 0 < t) :
    BoundedSpatialJets.Space Plane F k →L[ℝ] BoundedSpatialJets.Space Plane F k :=
  BoundedSpatialJets.convolutionCLM Plane F k volume (kernel t) (kernel_integrable ht)

/-- Convolution by one Cartesian derivative of the Gaussian. -/
def gradientOperator (k : ℕ) (t : ℝ) (ht : 0 < t) (j : Fin 2) :
    BoundedSpatialJets.Space Plane F k →L[ℝ] BoundedSpatialJets.Space Plane F k :=
  BoundedSpatialJets.convolutionCLM Plane F k volume (kernelDerivative t j)
    (kernelDerivative_integrable ht j)

theorem norm_heatOperator_le (k : ℕ) (t : ℝ) (ht : 0 < t) :
    ‖heatOperator F k t ht‖ ≤ 1 := by
  have h := BoundedSpatialJets.norm_convolutionCLM_le Plane F k volume
    (kernel t) (kernel_integrable ht)
  have hm : BoundedSpatialJets.kernelMass Plane volume (kernel t) = 1 := by
    unfold BoundedSpatialJets.kernelMass
    simp_rw [abs_of_nonneg (kernel_nonneg t _)]
    exact kernel_integral ht
  simpa only [heatOperator, hm] using h

theorem norm_gradientOperator_le (k : ℕ) (t : ℝ) (ht : 0 < t) (j : Fin 2) :
    ‖gradientOperator F k t ht j‖ ≤ 2 / Real.sqrt t :=
  (BoundedSpatialJets.norm_convolutionCLM_le Plane F k volume
    (kernelDerivative t j) (kernelDerivative_integrable ht j)).trans
      (kernelDerivative_abs_integral_le ht j)

/-- The zeroth component is the usual pointwise Gaussian convolution. -/
theorem heatOperator_apply (k : ℕ) (t : ℝ) (ht : 0 < t)
    (J : BoundedSpatialJets.Space Plane F k) (x : Plane) :
    BoundedSpatialJets.function Plane F k (heatOperator F k t ht J) x =
      ∫ y, kernel t y • BoundedSpatialJets.function Plane F k J (x - y) :=
  BoundedSpatialJets.function_convolution Plane F k volume (kernel t)
    (kernel_integrable ht) J x

theorem gradientOperator_apply (k : ℕ) (t : ℝ) (ht : 0 < t) (j : Fin 2)
    (J : BoundedSpatialJets.Space Plane F k) (x : Plane) :
    BoundedSpatialJets.function Plane F k (gradientOperator F k t ht j J) x =
      ∫ y, kernelDerivative t j y • BoundedSpatialJets.function Plane F k J (x - y) :=
  BoundedSpatialJets.function_convolution Plane F k volume (kernelDerivative t j)
    (kernelDerivative_integrable ht j) J x

/-- Every supplied derivative is transported by the same Gaussian kernel. -/
theorem heatOperator_jet (k : ℕ) (t : ℝ) (ht : 0 < t)
    (J : BoundedSpatialJets.Space Plane F k) (i : Fin (k + 1)) (x : Plane) :
    (heatOperator F k t ht J).val i x = ∫ y, kernel t y • J.val i (x - y) := rfl

theorem gradientOperator_jet (k : ℕ) (t : ℝ) (ht : 0 < t) (j : Fin 2)
    (J : BoundedSpatialJets.Space Plane F k) (i : Fin (k + 1)) (x : Plane) :
    (gradientOperator F k t ht j J).val i x =
      ∫ y, kernelDerivative t j y • J.val i (x - y) := rfl

theorem norm_heatOperator_apply_le (k : ℕ) (t : ℝ) (ht : 0 < t)
    (J : BoundedSpatialJets.Space Plane F k) : ‖heatOperator F k t ht J‖ ≤ ‖J‖ := by
  calc
    _ ≤ ‖heatOperator F k t ht‖ * ‖J‖ := (heatOperator F k t ht).le_opNorm J
    _ ≤ 1 * ‖J‖ := mul_le_mul_of_nonneg_right (norm_heatOperator_le F k t ht) (norm_nonneg J)
    _ = ‖J‖ := one_mul _

theorem norm_gradientOperator_apply_le (k : ℕ) (t : ℝ) (ht : 0 < t) (j : Fin 2)
    (J : BoundedSpatialJets.Space Plane F k) :
    ‖gradientOperator F k t ht j J‖ ≤ (2 / Real.sqrt t) * ‖J‖ :=
  ((gradientOperator F k t ht j).le_opNorm J).trans
    (mul_le_mul_of_nonneg_right (norm_gradientOperator_le F k t ht j) (norm_nonneg J))

end ForcedComputation.PlaneHeat

end

end OAI
