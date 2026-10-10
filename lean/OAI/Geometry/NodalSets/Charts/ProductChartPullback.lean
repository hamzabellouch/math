import Mathlib.LinearAlgebra.Basis.Prod
import OAI.Geometry.NodalSets.Charts.CircleChartFactor

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

def productFrame : Module.Basis (Fin 4 ⊕ Fin 1) ℝ Model :=
  (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.prod
    (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis

def productMetricMatrix (g : SmoothMetric) (p : Manifold5) (y : Model) :
    Matrix (Fin 4 ⊕ Fin 1) (Fin 4 ⊕ Fin 1) ℝ := fun i j ↦
  g.inner ((extChartAt modelWithCorners p).symm y)
    (mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y (productFrame i))
    (mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y (productFrame j))

lemma product_chart_target (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    y.1 ∈ (extChartAt (𝓡 4) p.1).target ∧ y.2 ∈ (extChartAt (𝓡 1) p.2).target := by
  rw [extChartAt_prod] at hy
  exact hy

lemma product_chart_inverse_derivative (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y =
      (mfderiv 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p.1).symm y.1).prodMap
      (mfderiv 𝓘(ℝ,CircleModel) (𝓡 1) (extChartAt (𝓡 1) p.2).symm y.2) := by
  have hb : MDifferentiableAt 𝓘(ℝ,BaseModel) (𝓡 4) (extChartAt (𝓡 4) p.1).symm y.1 := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 4) (product_chart_target p hy).1
    rw [ModelWithCorners.range_eq_univ,mdifferentiableWithinAt_univ] at h
    convert! h using 1
  have hc : MDifferentiableAt 𝓘(ℝ,CircleModel) (𝓡 1) (extChartAt (𝓡 1) p.2).symm y.2 := by
    have h := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡 1) (product_chart_target p hy).2
    rw [ModelWithCorners.range_eq_univ,mdifferentiableWithinAt_univ] at h
    convert! h using 1
  rw [show 𝓘(ℝ,Model) = 𝓘(ℝ,BaseModel).prod 𝓘(ℝ,CircleModel) from modelWithCornersSelf_prod,
    ← chartedSpaceSelf_prod]
  convert! mfderiv_prodMap hb hc using 1

lemma product_chart_embedding_derivative (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) (v : Model) :
    mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding ((extChartAt modelWithCorners p).symm y)
      (mfderiv 𝓘(ℝ,Model) modelWithCorners (extChartAt modelWithCorners p).symm y v) =
      (sphereChartDerivative p.1 y.1 v.1,circleChartDerivative p.2 y.2 v.2) := by
  rw [targetEmbedding_derivative,product_chart_inverse_derivative p hy]
  rfl

lemma sphereWeightedChartMatrix_apply (A : Matrix (Fin 5) (Fin 5) ℝ) (rho : ℝ)
    (p : Base) (y : BaseModel) (i j : Fin 4) :
    sphereWeightedChartMatrix A rho p y i j =
      ambientMatrixForm (weightedBaseMatrix A rho)
        (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ i))
        (sphereChartDerivative p y (EuclideanSpace.basisFun (Fin 4) ℝ j)) := by
  rw [ambientMatrixForm_dot]
  unfold sphereWeightedChartMatrix
  rw [Matrix.mul_assoc]
  simp only [mul_apply,transpose_apply,
    sphereChartFrame_apply,mulVec,dotProduct]

lemma independentAmbientMetric_productMatrix
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    (hA : ∀ i j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ A x i j))
    (hp : ∀ x, (A x).PosDef) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho)
    (hrp : ∀ x, 0 < rho x) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    productMetricMatrix (independentAmbientMetric A rho hA hp hr hrp) p y =
      fromBlocks (sphereWeightedChartMatrix (A ((extChartAt (𝓡 4) p.1).symm y.1))
        (rho ((extChartAt (𝓡 4) p.1).symm y.1)) p.1 y.1) 0 0
        (Matrix.of fun _ _ : Fin 1 ↦
          (ambientCircleWeight (A ((extChartAt (𝓡 4) p.1).symm y.1))
            (rho ((extChartAt (𝓡 4) p.1).symm y.1)))^2 * circleChartFactor p.2 y.2) := by
  ext i j
  change warpedAmbientForm _ _
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding _
      (mfderiv 𝓘(ℝ,Model) modelWithCorners _ y (productFrame i)))
    (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding _
      (mfderiv 𝓘(ℝ,Model) modelWithCorners _ y (productFrame j))) = _
  rw [product_chart_embedding_derivative p hy,product_chart_embedding_derivative p hy,
    warpedAmbientForm_apply]
  have hpnt : ((extChartAt modelWithCorners p).symm y).1 =
      (extChartAt (𝓡 4) p.1).symm y.1 := by
    rw [extChartAt_prod]
    rfl
  rw [hpnt]
  cases i <;> cases j <;>
    simp only [productFrame,Module.Basis.prod_apply_inl_fst,Module.Basis.prod_apply_inl_snd,
      Module.Basis.prod_apply_inr_fst,Module.Basis.prod_apply_inr_snd,
      OrthonormalBasis.coe_toBasis,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.of_apply,
      map_zero,inner_zero_left,inner_zero_right,mul_zero,zero_add,add_zero,
      sphereWeightedChartMatrix_apply,circleChartDerivative_inner_basis]
  all_goals simp

end
end Yau.Target

end OAI
