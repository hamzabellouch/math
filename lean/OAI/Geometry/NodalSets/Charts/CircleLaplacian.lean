import OAI.Geometry.NodalSets.Charts.SeparatedCircleDivergence
import OAI.Geometry.NodalSets.Elliptic.ProductFlux

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

lemma independentAmbientMetric_circle_laplacian (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    chartLaplacian (independentAmbientMetric A rho hA hp hr hrp)
      (extChartAt modelWithCorners p) (circleLift f) y =
    (baseChartDensity rho p.1 y.1)⁻¹ * ∑ i,
      fderiv ℝ (baseChartFlux A rho f p.1 i) y.1 (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  rw [chartLaplacian_product_basis _ p _ (fun i ↦
    (circleLift_product_flux_smooth_at A rho hA hp hr hrp hrad f hf p hy i).differentiableAt (by simp))]
  unfold basisMetricLaplacian
  rw [basisMetricMatrix_product,independentAmbientMetric_product_volume A rho hA hp hr hrp hrad p hy]
  have hd (i : Fin 4 ⊕ Fin 1) :=
    (circleLift_product_flux_eventually A rho hA hp hr hrp hrad f hf p hy i).fderiv_eq (𝕜 := ℝ)
  simp_rw [hd]
  exact separated_density_cancellation (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis (baseChartFlux A rho f p.1)
    (fun t ↦ Real.sqrt (circleChartFactor p.2 t)) (baseChartDensity rho p.1 y.1)
    (fun i ↦ (baseChartFlux_smooth_at A rho hA hp hr hrp f hf p.1
      (product_chart_target p hy).1 i).differentiableAt (by simp))
    ((circleChartDensity_smooth_at p.2 (product_chart_target p hy).2).differentiableAt (by simp))
    (Real.sqrt_pos.mpr (circleChartFactor_pos p.2 (product_chart_target p hy).2)).ne'

end
end Yau.Target

end OAI
