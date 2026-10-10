import OAI.Geometry.NodalSets.Charts.ProductChartPullback

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma ambientCircleWeight_chart_ratio (A : Matrix (Fin 5) (Fin 5) ℝ) (hA : A.PosDef)
    {rho : ℝ} (hr : 0 < rho) (p : Base) {y : BaseModel}
    (hy : y ∈ (extChartAt (𝓡 4) p).target)
    (hx : A *ᵥ (fun i ↦ ((extChartAt (𝓡 4) p).symm y : AmbientBase) i) =
      (fun i ↦ ((extChartAt (𝓡 4) p).symm y : AmbientBase) i)) :
    ambientCircleWeight A rho = rho /
      (Real.sqrt (sphereWeightedChartMatrix A rho p y).det /
        Real.sqrt (sphereRoundChartMatrix p y).det) := by
  rw [sphere_chart_volume_ratio A hA hr p hy hx,ambientCircleWeight]
  field_simp

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))

include hrad

lemma independentAmbientMetric_product_det (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det =
      (rho ((extChartAt (𝓡 4) p.1).symm y.1))^2 *
        (sphereRoundChartMatrix p.1 y.1).det * circleChartFactor p.2 y.2 := by
  rw [independentAmbientMetric_productMatrix A rho hA hp hr hrp p hy,
    det_fromBlocks_zero₂₁,det_fin_one]
  dsimp only [Matrix.of_apply]
  have he := radial_tangent_gram_det _ (hp _) (hrp ((extChartAt (𝓡 4) p.1).symm y.1)) _ (sphereChartFrame p.1 y.1)
    (hrad _) (sphere_radial_dot _) (sphereChartFrame_orthogonal p.1 y.1)
  change (sphereWeightedChartMatrix _ _ _ _).det = _ at he
  rw [he,ambientCircleWeight,div_pow,Real.sq_sqrt (hp _).det_pos.le]
  have halg (r d H k : ℝ) (hr0 : r ≠ 0) (hd0 : d ≠ 0) :
      (r^4/d)*H*(d/r^2*k) = r^2*H*k := by
    field_simp
  convert! halg _ _ _ _ (hrp ((extChartAt (𝓡 4) p.1).symm y.1)).ne'
    (hp ((extChartAt (𝓡 4) p.1).symm y.1)).det_pos.ne' using 1

lemma independentAmbientMetric_product_volume (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    Real.sqrt (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det =
      rho ((extChartAt (𝓡 4) p.1).symm y.1) *
        Real.sqrt (sphereRoundChartMatrix p.1 y.1).det * Real.sqrt (circleChartFactor p.2 y.2) := by
  rw [independentAmbientMetric_product_det A rho hA hp hr hrp hrad p hy,
    Real.sqrt_mul (mul_nonneg (sq_nonneg _) (sphereRoundChartMatrix_posDef p.1 (product_chart_target p hy).1).det_pos.le),
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (hrp _).le]

lemma independentAmbientMetric_product_det_pos (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    0 < (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det := by
  rw [independentAmbientMetric_product_det A rho hA hp hr hrp hrad p hy]
  exact mul_pos (mul_pos (sq_pos_of_pos (hrp _))
    (sphereRoundChartMatrix_posDef p.1 (product_chart_target p hy).1).det_pos)
    (circleChartFactor_pos p.2 (product_chart_target p hy).2)

end
end Yau.Target

end OAI
