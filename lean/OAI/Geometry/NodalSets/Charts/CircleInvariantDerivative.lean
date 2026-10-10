import OAI.Geometry.NodalSets.Charts.BaseChartFlux

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def circleLift (f : Base → ℝ) (x : Manifold5) : ℝ := f x.1

lemma circleLift_chart (f : Base → ℝ) (p : Manifold5) :
    circleLift f ∘ (extChartAt modelWithCorners p).symm =
      (f ∘ (extChartAt (𝓡 4) p.1).symm) ∘ Prod.fst := by
  rw [extChartAt_prod]
  rfl

lemma circleLift_chart_derivative (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    fderiv ℝ (circleLift f ∘ (extChartAt modelWithCorners p).symm) y =
      (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p.1).symm) y.1).comp
        (ContinuousLinearMap.fst ℝ BaseModel CircleModel) := by
  rw [circleLift_chart,fderiv_comp y
    ((smooth_inverse_chart_comp f hf p.1 (product_chart_target p hy).1).differentiableAt (by simp))
    differentiableAt_fst,fderiv_fst]

lemma circleLift_product_covector (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (i : Fin 4 ⊕ Fin 1) :
    fderiv ℝ (circleLift f ∘ (extChartAt modelWithCorners p).symm) y (productFrame i) =
      Sum.elim (fun j ↦ fderiv ℝ (f ∘ (extChartAt (𝓡 4) p.1).symm) y.1
        (EuclideanSpace.basisFun (Fin 4) ℝ j)) (fun _ ↦ 0) i := by
  rw [circleLift_chart_derivative f hf p hy]
  cases i <;> simp [productFrame]

end
end Yau.Target

end OAI
