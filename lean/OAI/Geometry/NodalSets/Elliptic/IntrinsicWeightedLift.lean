import OAI.Geometry.NodalSets.Charts.IntrinsicChartTensor
import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientBounds
import OAI.Geometry.NodalSets.Spectral.LiftedEigenfunction

namespace OAI

namespace Yau.Target
open Manifold Matrix
open scoped ContDiff RealInnerProductSpace
noncomputable section

variable (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x)

def intrinsicWeightedMetric : SmoothMetric :=
  independentAmbientMetric (intrinsicAmbientMatrix A) rho
    (intrinsicAmbientMatrix_smooth A hA) (intrinsicAmbientMatrix_posDef A hs hp) hr hrp

def intrinsicRoundFlux (f : Base → ℝ) (p : Base) (i : Fin 4) (z : BaseModel) : ℝ :=
  roundChartDensity p z * ∑ j, intrinsicSphereChartTensor A p z i j *
    fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ j)

def intrinsicWeightedChartOperator (f : Base → ℝ) (p : Base) (z : BaseModel) : ℝ :=
  (rho ((extChartAt (𝓡 4) p).symm z))⁻¹ * (roundChartDensity p z)⁻¹ *
    ∑ i, fderiv ℝ (intrinsicRoundFlux A f p i) z (EuclideanSpace.basisFun (Fin 4) ℝ i)

lemma intrinsicWeightedChartOperator_eq (f : Base → ℝ) (p : Base) (z : BaseModel) :
    intrinsicWeightedChartOperator A rho f p z =
      ambientWeightedChartOperator (intrinsicAmbientMatrix A) rho f p z := by
  have he : intrinsicRoundFlux A f p = roundTensorFlux (intrinsicAmbientMatrix A) f p := by
    funext i w
    simp only [intrinsicRoundFlux,roundTensorFlux,intrinsicSphereChartTensor_eq]
  rw [intrinsicWeightedChartOperator,ambientWeightedChartOperator,he]

lemma intrinsicWeightedMetric_lift (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Manifold5) {y : Model}
    (hy : y ∈ (extChartAt modelWithCorners p).target) :
    chartLaplacian (intrinsicWeightedMetric A hA hs hp rho hr hrp)
      (extChartAt modelWithCorners p) (circleLift f) y =
      intrinsicWeightedChartOperator A rho f p.1 y.1 := by
  rw [intrinsicWeightedChartOperator_eq]
  exact independentAmbientMetric_weighted_lift (intrinsicAmbientMatrix A) rho
    (intrinsicAmbientMatrix_smooth A hA) (intrinsicAmbientMatrix_posDef A hs hp) hr hrp
    (intrinsicAmbientMatrix_radial A) f hf p hy

lemma intrinsicWeightedMetric_comparison (a b r R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hr0 : 0 < r)
    (hlo : ∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
      a*‖v‖^2 ≤ A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v))
    (hhi : ∀ (x : Base) (v : AmbientBase), ⟪(x : AmbientBase),v⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x v) ≤ b*‖v‖^2)
    (hrho : ∀ x, r ≤ rho x) (hR : ∀ x, rho x ≤ R)
    (x : Manifold5) (v : TangentSpace modelWithCorners x) :
    min (r / max b 1) ((min a 1)^5/R^2) * roundProductMetric.inner x v v ≤
      (intrinsicWeightedMetric A hA hs hp rho hr hrp).inner x v v ∧
    (intrinsicWeightedMetric A hA hs hp rho hr hrp).inner x v v ≤
      max (R / min a 1) ((max b 1)^5/r^2) * roundProductMetric.inner x v v := by
  exact independentAmbientMetric_original_comparison (min a 1) (max b 1) r R
    (lt_min ha zero_lt_one) (lt_max_of_lt_left hb) hr0
    (intrinsicAmbientMatrix A) rho (intrinsicAmbientMatrix_smooth A hA)
    (intrinsicAmbientMatrix_posDef A hs hp) hr hrp
    (fun x v ↦ (intrinsicAmbientMatrix_bounds A a b hlo hhi x v).1)
    (fun x v ↦ (intrinsicAmbientMatrix_bounds A a b hlo hhi x v).2) hrho hR x v

end
end Yau.Target

end OAI
