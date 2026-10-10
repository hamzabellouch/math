import OAI.Geometry.EinsteinFour.MetricCurvatureGreen

namespace OAI

/-! The opposite curvature block acting on the plus Weyl gradient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory TraceHessian Angular
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frameMinusCoefficient (g : SmoothMetric M) (p : Averages.CurvatureIndex)
    (e : FrameBundle g) : ℝ :=
  blockTensor (minusWeyl g e.base e.frame) oppositeMatrix p.1.1 p.1.2 p.2.2 p.2.1

def frameMinusCoefficientDerivative (g : SmoothMetric M) (p : Averages.CurvatureIndex)
    (e : FrameBundle g) : ℝ :=
  blockTensor (minusWeylGradient g e.base e.frame p.1.2)
    oppositeMatrix p.1.1 p.1.2 p.2.2 p.2.1

/-- The derivative-slot Green formula on the actual metric tensors.
The third derivatives retain their order; the half factor is proved by
skewing the first two slots, before any Ricci substitution. -/
theorem weighted_metric_minus_curvature_green
    (g : SmoothMetric M) {μ : Measure (FrameBundle g)}
    [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]
    (φ : Fin 4 → FrameFlow g μ)
    (m : C(FrameBundle g, ℝ)) (dm : Fin 4 → C(FrameBundle g, ℝ))
    (hA : ∀ p, Continuous (frameMinusCoefficient g p))
    (hDA : ∀ p, Continuous (frameMinusCoefficientDerivative g p))
    (hZ : ∀ j, Continuous (frameGradientSlice g j))
    (hX : ∀ i j, Continuous (frameHessianSlice g i j))
    (hD : ∀ i k j, Continuous (frameThirdSlice g i k j))
    (hdiv : ∀ i j l e, (∑ k, frameMinusCoefficientDerivative g ((i, k), (j, l)) e) = 0)
    (hskew : ∀ i k j l e, frameMinusCoefficient g ((k, i), (j, l)) e =
      -frameMinusCoefficient g ((i, k), (j, l)) e)
    (hm : ∀ k t e, HasDerivAt (fun s => m ((φ k).map s e)) (dm k ((φ k).map t e)) t)
    (hAd : ∀ p t e, HasDerivAt
      (fun s => frameMinusCoefficient g p ((φ p.1.2).map s e))
      (frameMinusCoefficientDerivative g p ((φ p.1.2).map t e)) t)
    (hZd : ∀ k j t e, HasDerivAt (fun s => frameGradientSlice g j ((φ k).map s e))
      (frameHessianSlice g k j ((φ k).map t e)) t)
    (hXd : ∀ k i j t e, HasDerivAt (fun s => frameHessianSlice g i j ((φ k).map s e))
      (frameThirdSlice g k i j ((φ k).map t e)) t) :
    (∫ e, ∑ p : Averages.CurvatureIndex,
      (m e * frameMinusCoefficient g p e *
        matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
          (plusWeylHessian g e.base e.frame p.1.2 p.2.2) +
        dm p.1.2 e * frameMinusCoefficient g p e *
          matrixPairing (plusWeylHessian g e.base e.frame p.1.1 p.2.1)
            (plusWeylGradient g e.base e.frame p.2.2)) ∂μ) =
      (1 / 2 : ℝ) * (∫ e, ∑ p : Averages.CurvatureIndex,
        m e * frameMinusCoefficient g p e *
          inner ℝ (frameThirdSlice g p.1.1 p.1.2 p.2.1 e -
            frameThirdSlice g p.1.2 p.1.1 p.2.1 e)
            (frameGradientSlice g p.2.2 e) ∂μ) := by
  have h := Averages.weighted_curvature_green μ
    (fun k => (φ k).map) (fun k => (φ k).continuous) (fun k => (φ k).preserves)
    m dm (fun p => ⟨frameMinusCoefficient g p, hA p⟩)
    (fun p => ⟨frameMinusCoefficientDerivative g p, hDA p⟩)
    (fun j => ⟨frameGradientSlice g j, hZ j⟩)
    (fun i j => ⟨frameHessianSlice g i j, hX i j⟩)
    (fun i k j => ⟨frameThirdSlice g i k j, hD i k j⟩)
    hdiv hskew hm hAd hZd hXd
  simpa only [ContinuousMap.coe_mk, frameHessianSlice, frameGradientSlice,
    inner_matrixVector] using h


end
end PositiveEinsteinFour.Geometry

end OAI
