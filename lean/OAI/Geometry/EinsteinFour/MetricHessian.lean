import OAI.Geometry.EinsteinFour.MetricBianchi
import OAI.Geometry.EinsteinFour.FlowGreen
import OAI.Geometry.EinsteinFour.FrameFlow
import OAI.Geometry.EinsteinFour.TensorPairing

namespace OAI

/-! The weighted rough-Laplacian identity for the metric's actual Weyl
gradient. Differentiation takes place in the coordinate connection before
the parallel frame is applied. The integration identity follows from
frame-flow invariance, rather than an assumed Hessian integral formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Angular TraceHessian
open scoped Manifold ContDiff

noncomputable section

abbrev GradientVector := EuclideanSpace ℝ (Fin 4 × Fin 3 × Fin 3)

def gradientVector (Z : Gradient) : GradientVector :=
  WithLp.toLp 2 (fun p => Z p.1 p.2.1 p.2.2)

theorem gradientVector_norm_sq (Z : Gradient) :
    ‖gradientVector Z‖ ^ 2 = gradientSquareNorm Z := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ p : Fin 4 × Fin 3 × Fin 3, Z p.1 p.2.1 p.2.2 ^ 2) = _
  simp only [Fintype.sum_prod_type, gradientSquareNorm, squareNorm]

theorem gradientVector_hessian_norm (X : Hessian) :
    (∑ i, ‖gradientVector (X i)‖ ^ 2) = hessianNormSq X := by
  simp_rw [gradientVector_norm_sq]
  rw [← hessianPairing_self]
  simpa only [gradientSquareNorm, squareNorm, Fintype.sum_prod_type,
    tensorCoordinates, pow_two] using tensorCoordinates_pairing X X

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- Three successive covariant derivatives, retaining all derivative slots. -/
def plusWeylThirdDerivative (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j k : Fin 4) : Mat3 :=
  blockCoordinates (fun a =>
    frameTensor e.matrix
      (covariantDerivative g c
        (covariantDerivative g c (covariantDerivative g c (normalizedWeylCoordinates g c)))
        (chartAt FourSpace c c))
      (Fin.cons i (Fin.cons j (Fin.cons k a)))) quaternionMatrix

def frameGradientVector (g : SmoothMetric M) (e : FrameBundle g) : GradientVector :=
  gradientVector (plusWeylGradient g e.base e.frame)

def frameHessianVector (g : SmoothMetric M) (i : Fin 4) (e : FrameBundle g) :
    GradientVector := gradientVector (plusWeylHessian g e.base e.frame i)

def frameThirdVector (g : SmoothMetric M) (i j : Fin 4) (e : FrameBundle g) :
    GradientVector := gradientVector (plusWeylThirdDerivative g e.base e.frame i j)

/-- The actual rough Laplacian of the Weyl gradient, in the same frame. -/
def frameGradientLaplacian (g : SmoothMetric M) (e : FrameBundle g) : GradientVector :=
  ∑ i, frameThirdVector g i i e

/-- Weighted integration by parts for the actual covariant Hessian. The
classical parallel-frame differentiation identities and measure-preserving
flows are explicit; no new weighted estimate is a hypothesis. -/
theorem weighted_metric_hessian_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hZ : Continuous (frameGradientVector g))
    (hX : ∀ i, Continuous (frameHessianVector g i))
    (hXX : ∀ i, Continuous (frameThirdVector g i i))
    (hm : ∀ i t e, HasDerivAt (fun s => m ((φ i).map s e))
      (dm i ((φ i).map t e)) t)
    (hZd : ∀ i t e, HasDerivAt (fun s => frameGradientVector g ((φ i).map s e))
      (frameHessianVector g i ((φ i).map t e)) t)
    (hXd : ∀ i t e, HasDerivAt (fun s => frameHessianVector g i ((φ i).map s e))
      (frameThirdVector g i i ((φ i).map t e)) t) :
    (∫ e, m e * hessianNormSq (plusWeylHessian g e.base e.frame) +
      ∑ i, dm i e * inner ℝ (frameGradientVector g e) (frameHessianVector g i e) ∂μ) =
      -(∫ e, m e * inner ℝ (frameGradientVector g e) (frameGradientLaplacian g e) ∂μ) := by
  have h := Averages.weighted_four_direction_green μ
    (fun i => (φ i).map) (fun i => (φ i).continuous) (fun i => (φ i).preserves)
    m dm ⟨frameGradientVector g, hZ⟩
    (fun i => ⟨frameHessianVector g i, hX i⟩)
    (fun i => ⟨frameThirdVector g i i, hXX i⟩) hm hZd hXd
  simpa only [ContinuousMap.coe_mk, frameHessianVector, gradientVector_hessian_norm,
    frameGradientLaplacian] using h

end

end PositiveEinsteinFour.Geometry

end OAI
