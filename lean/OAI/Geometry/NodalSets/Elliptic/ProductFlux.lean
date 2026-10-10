import OAI.Geometry.NodalSets.Charts.CircleInvariantDerivative
import OAI.Geometry.NodalSets.Charts.ProductChartFlux
import OAI.Geometry.NodalSets.Elliptic.TargetLaplacianBasis

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff Topology
noncomputable section
variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (f : Base → ℝ) (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f)

include hrad hf

lemma circleLift_actual_product_flux (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i y =
    Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 y.2) * baseChartFlux A rho f p.1 j y.1)
      (fun _ ↦ 0) i := by
  unfold basisMetricFlux
  simp only [basisMetricMatrix_product,circleLift_product_covector f hf p hy]
  exact independentAmbientMetric_product_flux A rho hA hp hr hrp hrad p hy _ i

lemma circleLift_product_flux_eventually (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i =ᶠ[𝓝 y]
    (fun w ↦ Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 w.2) * baseChartFlux A rho f p.1 j w.1)
      (fun _ ↦ 0) i) := by
  filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with w hw
  exact circleLift_actual_product_flux A rho hA hp hr hrp hrad f hf p hw i

lemma circleLift_product_flux_smooth_at (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    ContDiffAt ℝ ∞ (basisMetricFlux productFrame
      (chartBilinearForm (independentAmbientMetric A rho hA hp hr hrp) (extChartAt modelWithCorners p))
      (circleLift f ∘ (extChartAt modelWithCorners p).symm) i) y := by
  have hs : ContDiffAt ℝ ∞
      (fun w : Model ↦ Sum.elim (fun j ↦ Real.sqrt (circleChartFactor p.2 w.2) *
        baseChartFlux A rho f p.1 j w.1) (fun _ ↦ 0) i) y := by
    cases i with
    | inl j =>
      exact ((circleChartDensity_smooth_at p.2 (product_chart_target p hy).2).comp y contDiffAt_snd).mul
        ((baseChartFlux_smooth_at A rho hA hp hr hrp f hf p.1 (product_chart_target p hy).1 j).comp y contDiffAt_fst)
    | inr j => exact contDiffAt_const
  exact hs.congr_of_eventuallyEq
    (circleLift_product_flux_eventually A rho hA hp hr hrp hrad f hf p hy i)

end
end Yau.Target

end OAI
