import OAI.Geometry.EinsteinFour.MatrixSlotOperator
import OAI.Geometry.EinsteinFour.OperatorGreen

namespace OAI

/-! The varying-coefficient Green identity for the actual Weyl matrix slot. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian
open scoped Manifold ContDiff

noncomputable section

local instance : NormedAddCommGroup Mat := Matrix.frobeniusNormedAddCommGroup
local instance : NormedSpace ℝ Mat := Matrix.frobeniusNormedSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameWeylMatrix (g : SmoothMetric M) (e : FrameBundle g) : Mat :=
  plusWeyl g e.base e.frame

def frameWeylGradientMatrix (g : SmoothMetric M) (i : Fin 4) (e : FrameBundle g) : Mat :=
  plusWeylGradient g e.base e.frame i

def frameWeylHessianMatrix (g : SmoothMetric M) (i j : Fin 4) (e : FrameBundle g) : Mat :=
  plusWeylHessian g e.base e.frame i j

/-- The first-derivative and Laplacian corrections in the nonparallel
matrix-slot term follow from differentiating the actual Weyl coefficient.
No derivative of a chosen eigenframe occurs. -/
theorem weighted_metric_matrix_slot_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hT : Continuous (frameWeylMatrix g))
    (hDT : ∀ i, Continuous (frameWeylGradientMatrix g i))
    (hDDT : ∀ i, Continuous (frameWeylHessianMatrix g i i))
    (hZ : Continuous (frameGradientVector g))
    (hX : ∀ i, Continuous (frameHessianVector g i))
    (hXX : ∀ i, Continuous (frameThirdVector g i i))
    (hDsym : ∀ i e, symmetric (frameWeylGradientMatrix g i e))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((φ i).map s e))
      (dm i ((φ i).map t e)) t)
    (hTd : ∀ i t e, HasDerivAt (fun s => frameWeylMatrix g ((φ i).map s e))
      (frameWeylGradientMatrix g i ((φ i).map t e)) t)
    (hDTd : ∀ i t e, HasDerivAt (fun s => frameWeylGradientMatrix g i ((φ i).map s e))
      (frameWeylHessianMatrix g i i ((φ i).map t e)) t)
    (hZd : ∀ i t e, HasDerivAt (fun s => frameGradientVector g ((φ i).map s e))
      (frameHessianVector g i ((φ i).map t e)) t)
    (hXd : ∀ i t e, HasDerivAt (fun s => frameHessianVector g i ((φ i).map s e))
      (frameThirdVector g i i ((φ i).map t e)) t) :
    (∫ e, m e * (∑ i, inner ℝ (frameHessianVector g i e)
        (matrixSlotOperator (frameWeylMatrix g e) (frameHessianVector g i e))) +
      ∑ i, dm i e * inner ℝ (frameGradientVector g e)
        (matrixSlotOperator (frameWeylMatrix g e) (frameHessianVector g i e)) ∂μ) =
      -(∫ e, m e * inner ℝ (frameGradientVector g e)
        (matrixSlotOperator (frameWeylMatrix g e) (frameGradientLaplacian g e)) ∂μ) +
      (1 / 2 : ℝ) * (∫ e, m e * inner ℝ (frameGradientVector g e)
        (∑ i, matrixSlotOperator (frameWeylHessianMatrix g i i e) (frameGradientVector g e)) +
        ∑ i, dm i e * inner ℝ (frameGradientVector g e)
          (matrixSlotOperator (frameWeylGradientMatrix g i e) (frameGradientVector g e)) ∂μ) := by
  let A : C(FrameBundle g, GradientVector →L[ℝ] GradientVector) :=
    ⟨fun e => matrixSlot (frameWeylMatrix g e), matrixSlot.continuous.comp hT⟩
  let dA (i : Fin 4) : C(FrameBundle g, GradientVector →L[ℝ] GradientVector) :=
    ⟨fun e => matrixSlot (frameWeylGradientMatrix g i e), matrixSlot.continuous.comp (hDT i)⟩
  let ddA (i : Fin 4) : C(FrameBundle g, GradientVector →L[ℝ] GradientVector) :=
    ⟨fun e => matrixSlot (frameWeylHessianMatrix g i i e), matrixSlot.continuous.comp (hDDT i)⟩
  have h := Averages.weighted_four_operator_green μ
    (fun i => (φ i).map) (fun i => (φ i).continuous) (fun i => (φ i).preserves)
    m dm ⟨frameGradientVector g, hZ⟩
    (fun i => ⟨frameHessianVector g i, hX i⟩)
    (fun i => ⟨frameThirdVector g i i, hXX i⟩) A dA ddA
    (fun i e u v => matrixSlotOperator_selfadjoint _ (hDsym i e) u v)
    hm hZd hXd
    (fun i t e => hasDerivAt_matrixSlot (hTd i t e))
    (fun i t e => hasDerivAt_matrixSlot (hDTd i t e))
  simpa only [A, dA, ddA, ContinuousMap.coe_mk, matrixSlot_apply,
    frameGradientLaplacian] using h

end

end PositiveEinsteinFour.Geometry

end OAI
