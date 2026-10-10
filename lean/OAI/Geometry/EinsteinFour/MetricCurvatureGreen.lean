import OAI.Geometry.EinsteinFour.CurvatureGreen
import OAI.Geometry.EinsteinFour.MetricHessian

namespace OAI

/-! Derivative-slot integration for the actual metric Weyl Hessian. The
coefficient and its derivative are both the concrete quaternion curvature
block. The only differential premises are parallel differentiation and
the classical divergence and skew identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

abbrev MatrixVector := EuclideanSpace ℝ (Fin 3 × Fin 3)

def matrixVector (A : Mat) : MatrixVector := WithLp.toLp 2 (fun p => A p.1 p.2)

theorem inner_matrixVector (A B : Mat) :
    inner ℝ (matrixVector A) (matrixVector B) = matrixPairing A B := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    matrixVector, Fintype.sum_prod_type, matrixPairing]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameGradientSlice (g : SmoothMetric M) (j : Fin 4) (e : FrameBundle g) : MatrixVector :=
  matrixVector (plusWeylGradient g e.base e.frame j)

def frameHessianSlice (g : SmoothMetric M) (i j : Fin 4) (e : FrameBundle g) : MatrixVector :=
  matrixVector (plusWeylHessian g e.base e.frame i j)

def frameThirdSlice (g : SmoothMetric M) (i k j : Fin 4) (e : FrameBundle g) : MatrixVector :=
  matrixVector (plusWeylThirdDerivative g e.base e.frame i k j)

def framePlusCoefficient (g : SmoothMetric M) (p : Averages.CurvatureIndex)
    (e : FrameBundle g) : ℝ :=
  blockTensor (plusWeyl g e.base e.frame) quaternionMatrix p.1.1 p.1.2 p.2.2 p.2.1

def framePlusCoefficientDerivative (g : SmoothMetric M) (p : Averages.CurvatureIndex)
    (e : FrameBundle g) : ℝ :=
  blockTensor (plusWeylGradient g e.base e.frame p.1.2)
    quaternionMatrix p.1.1 p.1.2 p.2.2 p.2.1

/-- The derivative-slot Green formula on the actual metric tensors.
The third derivatives retain their order; the half factor is proved by
skewing the first two slots, before any Ricci substitution. -/
theorem weighted_metric_curvature_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hA : ∀ p, Continuous (framePlusCoefficient g p))
    (hDA : ∀ p, Continuous (framePlusCoefficientDerivative g p))
    (hZ : ∀ j, Continuous (frameGradientSlice g j))
    (hX : ∀ i j, Continuous (frameHessianSlice g i j))
    (hD : ∀ i k j, Continuous (frameThirdSlice g i k j))
    (hdiv : ∀ i j l e, (∑ k, framePlusCoefficientDerivative g ((i, k), (j, l)) e) = 0)
    (hskew : ∀ i k j l e, framePlusCoefficient g ((k, i), (j, l)) e =
      -framePlusCoefficient g ((i, k), (j, l)) e)
    (hm : ∀ k t e, HasDerivAt (fun s => m ((φ k).map s e)) (dm k ((φ k).map t e)) t)
    (hAd : ∀ p t e, HasDerivAt
      (fun s => framePlusCoefficient g p ((φ p.1.2).map s e))
      (framePlusCoefficientDerivative g p ((φ p.1.2).map t e)) t)
    (hZd : ∀ k j t e, HasDerivAt (fun s => frameGradientSlice g j ((φ k).map s e))
      (frameHessianSlice g k j ((φ k).map t e)) t)
    (hXd : ∀ k i j t e, HasDerivAt (fun s => frameHessianSlice g i j ((φ k).map s e))
      (frameThirdSlice g k i j ((φ k).map t e)) t) :
    (∫ e, ∑ p : Averages.CurvatureIndex,
      (m e * framePlusCoefficient g p e *
        matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
          (plusWeylHessian g e.base e.frame p.1.2 p.2.2) +
        dm p.1.2 e * framePlusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylGradient g e.base e.frame p.2.2)) ∂μ) =
      (1 / 2 : ℝ) * (∫ e, ∑ p : Averages.CurvatureIndex,
        m e * framePlusCoefficient g p e *
          inner ℝ (frameThirdSlice g p.1.1 p.1.2 p.2.1 e -
            frameThirdSlice g p.1.2 p.1.1 p.2.1 e)
            (frameGradientSlice g p.2.2 e) ∂μ) := by
  have h := Averages.weighted_curvature_green μ
    (fun k => (φ k).map) (fun k => (φ k).continuous) (fun k => (φ k).preserves)
    m dm (fun p => ⟨framePlusCoefficient g p, hA p⟩)
    (fun p => ⟨framePlusCoefficientDerivative g p, hDA p⟩)
    (fun j => ⟨frameGradientSlice g j, hZ j⟩)
    (fun i j => ⟨frameHessianSlice g i j, hX i j⟩)
    (fun i k j => ⟨frameThirdSlice g i k j, hD i k j⟩)
    hdiv hskew hm hAd hZd hXd
  simpa only [ContinuousMap.coe_mk, frameHessianSlice, frameGradientSlice,
    inner_matrixVector] using h

end
end PositiveEinsteinFour.Geometry

end OAI
