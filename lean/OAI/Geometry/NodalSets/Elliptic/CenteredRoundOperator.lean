import Mathlib.Analysis.InnerProductSpace.Laplacian
import OAI.Geometry.NodalSets.Charts.CenteredSphereDensity
import OAI.Geometry.NodalSets.Elliptic.WeightedLift

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma sphereChartTensor_one (p : Base) (y : BaseModel) :
    sphereChartTensor (fun _ ↦ (1 : Matrix (Fin 5) (Fin 5) ℝ)) p y =
      (sphereRoundChartMatrix p y)⁻¹ := by
  unfold sphereChartTensor
  rw [sphereChart_contravariant _ PosDef.one (show (0:ℝ)<1 by norm_num) p
    (by rw [centeredSphereChart_target]; trivial) (by simp)]
  simp [sphereWeightedChartMatrix,Yau.Geometry.weightedBaseMatrix,sphereRoundChartMatrix]

lemma centeredRoundTensorFlux_derivative (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (i : Fin 4) (v : BaseModel) :
    fderiv ℝ (roundTensorFlux (fun _ ↦ 1) f p i) 0 v =
      fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm)) 0 v
        (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  let Q := f ∘ (extChartAt (𝓡 4) p).symm
  have hQ : DifferentiableAt ℝ (fderiv ℝ Q) 0 :=
    (smooth_inverse_chart_derivative f hf p
      (by rw [centeredSphereChart_target]; trivial)).differentiableAt (by simp)
  have hd (j : Fin 4) := hQ.hasFDerivAt.clm_apply
    (hasFDerivAt_const (EuclideanSpace.basisFun (Fin 4) ℝ j) (0:BaseModel))
  have hc (j : Fin 4) := (centeredRoundChartDensity_hasFDerivAt p).mul
    (centeredSphereRoundInv_hasFDerivAt p i j)
  have h := HasFDerivAt.sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) ↦ (hc j).mul (hd j))
  have he : roundTensorFlux (fun _ ↦ 1) f p i =
      (fun y ↦ ∑ j, (roundChartDensity p y * (sphereRoundChartMatrix p y)⁻¹ i j) *
        fderiv ℝ Q y (EuclideanSpace.basisFun (Fin 4) ℝ j)) := by
    funext y
    simp [roundTensorFlux,sphereChartTensor_one,Finset.mul_sum,mul_assoc,Q]
  rw [he]
  change HasFDerivAt (fun y ↦ ∑ j, (roundChartDensity p y * (sphereRoundChartMatrix p y)⁻¹ i j) *
    fderiv ℝ Q y (EuclideanSpace.basisFun (Fin 4) ℝ j)) _ 0 at h
  rw [h.fderiv]
  simp [centeredRoundChartDensity,centeredSphereRoundMatrix,Matrix.one_apply,Q]

lemma centeredRoundOperator (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) :
    ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) f p
      (extChartAt (𝓡 4) p p) =
      ∑ i, fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm)) 0
        (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  rw [centeredSphereChart_value]
  simp [ambientWeightedChartOperator,centeredRoundChartDensity,
    centeredRoundTensorFlux_derivative f hf]

end
end Yau.Target

end OAI
