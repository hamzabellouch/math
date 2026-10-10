import OAI.Geometry.NodalSets.Charts.TargetChartBasis
import OAI.Geometry.NodalSets.Elliptic.BasisLaplacianReindex

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
noncomputable section

lemma basisMetricMatrix_target (g : SmoothMetric) (c : PartialEquiv Manifold5 Model) (y : Model) :
    basisMetricMatrix frame (chartBilinearForm g c y) = metricMatrix g c y := by
  ext i j
  simp only [basisMetricMatrix,LinearMap.toMatrix₂_apply,chartBilinearForm,metricMatrix]
  rfl

lemma basisMetricMatrix_product (g : SmoothMetric) (p : Manifold5) (y : Model) :
    basisMetricMatrix productFrame (chartBilinearForm g (extChartAt modelWithCorners p) y) =
      productMetricMatrix g p y := by
  ext i j
  simp only [basisMetricMatrix,LinearMap.toMatrix₂_apply,chartBilinearForm,productMetricMatrix]
  rfl

lemma chartLaplacian_basisMetricLaplacian (g : SmoothMetric)
    (c : PartialEquiv Manifold5 Model) (u : Manifold5 → ℝ) (y : Model) :
    chartLaplacian g c u y = basisMetricLaplacian frame (chartBilinearForm g c) (u ∘ c.symm) y := by
  simp only [basisMetricLaplacian,basisMetricMatrix_target,
    chartLaplacian,volumeFactor]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  funext z
  simp only [basisMetricFlux,basisMetricMatrix_target]

lemma chartLaplacian_product_basis (g : SmoothMetric) (p : Manifold5)
    (u : Manifold5 → ℝ) {y : Model}
    (hF : ∀ i, DifferentiableAt ℝ
      (basisMetricFlux productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
        (u ∘ (extChartAt modelWithCorners p).symm) i) y) :
    chartLaplacian g (extChartAt modelWithCorners p) u y =
      basisMetricLaplacian productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
        (u ∘ (extChartAt modelWithCorners p).symm) y := by
  rw [chartLaplacian_basisMetricLaplacian]
  have hr (i : Index) :
      basisMetricFlux indexedProductFrame (chartBilinearForm g (extChartAt modelWithCorners p))
          (u ∘ (extChartAt modelWithCorners p).symm) i =
      basisMetricFlux productFrame (chartBilinearForm g (extChartAt modelWithCorners p))
          (u ∘ (extChartAt modelWithCorners p).symm) (productIndexEquiv.symm i) := by
    funext z
    exact basisMetricFlux_reindex productFrame productIndexEquiv _ _ i z
  rw [basisMetricLaplacian_change indexedProductFrame frame _ _ (fun i ↦ by rw [hr]; exact hF _)]
  exact basisMetricLaplacian_reindex productFrame productIndexEquiv _ _ y

end
end Yau.Target

end OAI
