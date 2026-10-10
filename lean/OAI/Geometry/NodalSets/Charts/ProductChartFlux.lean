import OAI.Geometry.NodalSets.Charts.ProductChartVolume

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma positive_circle_block_inverse {H : Matrix (Fin 4) (Fin 4) ℝ} (hH : H.PosDef)
    {d : ℝ} (hd : 0 < d) :
    (fromBlocks H 0 0 (Matrix.of (fun _ _ : Fin 1 ↦ d)))⁻¹ =
      fromBlocks H⁻¹ 0 0 (Matrix.of (fun _ _ : Fin 1 ↦ d))⁻¹ := by
  have hD : IsUnit (Matrix.of (fun _ _ : Fin 1 ↦ d)) := by
    rw [Matrix.isUnit_iff_isUnit_det,det_fin_one]
    exact isUnit_iff_ne_zero.mpr hd.ne'
  rw [inv_fromBlocks_zero₂₁_of_isUnit_iff H 0 _ (iff_of_true hH.isUnit hD)]
  simp

variable (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x)

lemma independentAmbientMetric_product_inverse (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y)⁻¹ =
      fromBlocks (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
        (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1)⁻¹ 0 0
        (Matrix.of fun _ _ : Fin 1 ↦
          (ambientCircleWeight (A ((extChartAt (𝓡 4) p.1).symm y.1))
            (rho ((extChartAt (𝓡 4) p.1).symm y.1)))^2 * circleChartFactor p.2 y.2)⁻¹ := by
  rw [independentAmbientMetric_productMatrix A rho hA hp hr hrp p hy]
  apply positive_circle_block_inverse
    (sphereWeightedChartMatrix_posDef _ (hp _) (hrp _) p.1 (product_chart_target p hy).1)
  exact mul_pos (sq_pos_of_pos (ambientCircleWeight_pos _ (hp _) (hrp _)))
    (circleChartFactor_pos p.2 (product_chart_target p hy).2)

lemma independentAmbientMetric_product_flux
    (hrad : ∀ x : Base, A x *ᵥ (fun i ↦ (x : AmbientBase) i) = (fun i ↦ (x : AmbientBase) i))
    (p : Manifold5) {y : Model} (hy : y ∈ (extChartAt modelWithCorners p).target)
    (v : Fin 4 → ℝ) (i : Fin 4 ⊕ Fin 1) :
    Real.sqrt (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y).det *
      ∑ j, (productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y)⁻¹ i j *
        Sum.elim v (fun _ ↦ 0) j =
    Sum.elim (fun a ↦ Real.sqrt (circleChartFactor p.2 y.2) *
      (rho ((extChartAt (𝓡 4) p.1).symm y.1) * Real.sqrt (sphereRoundChartMatrix p.1 y.1).det *
        ∑ b, (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
          (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1)⁻¹ a b * v b)) (fun _ ↦ 0) i := by
  rw [independentAmbientMetric_product_volume A rho hA hp hr hrp hrad p hy,
    independentAmbientMetric_product_inverse A rho hA hp hr hrp p hy]
  cases i with
  | inl a =>
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,fromBlocks_apply₁₁,
      fromBlocks_apply₁₂,mul_zero,Finset.sum_const_zero,add_zero]
    ring
  | inr a => simp [Fintype.sum_sum_type,Matrix.fromBlocks]

end
end Yau.Target

end OAI
