import OAI.Geometry.NodalSets.Charts.SphereChartConformal
import OAI.Geometry.NodalSets.Elliptic.CenteredRoundOperator

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma roundTensorFlux_conformal (f : Base → ℝ) (p : Base) (i : Fin 4) (y : BaseModel) :
    roundTensorFlux (fun _ ↦ 1) f p i y =
      (4/(‖y‖^2+4))^2 *
        fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) y (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  rw [roundTensorFlux,roundChartDensity_conformal,sphereChartTensor_one,
    sphereRoundChartMatrix_inverse_conformal]
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hn : 4/(‖y‖^2+4) ≠ 0 := by positivity
  field_simp

lemma roundConformalSquare_hasFDerivAt (y : BaseModel) :
    HasFDerivAt (fun z : BaseModel ↦ (4/(‖z‖^2+4))^2)
      ((-64/(‖y‖^2+4)^3) • innerSL ℝ y) y := by
  have h := ((stereoReciprocal_hasFDerivAt y).const_mul 4).pow 2
  convert! h using 1
  ext v
  simp [stereoReciprocal,smul_eq_mul,div_eq_mul_inv]
  field_simp
  ring

lemma roundTensorFlux_fixed_derivative (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (y : BaseModel) (i : Fin 4) :
    fderiv ℝ (roundTensorFlux (fun _ ↦ 1) f p i) y (EuclideanSpace.basisFun (Fin 4) ℝ i) =
      (-64/(‖y‖^2+4)^3)*y i *
        fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) y (EuclideanSpace.basisFun (Fin 4) ℝ i) +
      (4/(‖y‖^2+4))^2 *
        fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm)) y
          (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ i) := by
  have hd := ((smooth_inverse_chart_derivative f hf p
    (by rw [centeredSphereChart_target]; trivial)).differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (EuclideanSpace.basisFun (Fin 4) ℝ i) y)
  have h := (roundConformalSquare_hasFDerivAt y).mul hd
  have he : roundTensorFlux (fun _ ↦ 1) f p i = fun z ↦ (4/(‖z‖^2+4))^2 *
      fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ i) :=
    funext (roundTensorFlux_conformal f p i)
  change HasFDerivAt (fun z ↦ (4/(‖z‖^2+4))^2 *
    fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) _ y at h
  rw [he,h.fderiv]
  simp [EuclideanSpace.inner_single_right,smul_eq_mul]
  ring

theorem fixedChartRoundOperator (f : Base → ℝ)
    (hf : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ f) (p : Base) (y : BaseModel) :
    ambientWeightedChartOperator (fun _ ↦ 1) (fun _ ↦ 1) f p y =
      ((‖y‖^2+4)^2/16) *
        (∑ i, fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm)) y
          (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ i)) -
      ((‖y‖^2+4)/4) *
        (∑ i, y i * fderiv ℝ (f ∘ (extChartAt (𝓡 4) p).symm) y
          (EuclideanSpace.basisFun (Fin 4) ℝ i)) := by
  simp only [ambientWeightedChartOperator,inv_one,one_mul,roundChartDensity_conformal,
    roundTensorFlux_fixed_derivative f hf,Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
  have hd : ‖y‖^2+4 ≠ 0 := by positivity
  field_simp
  ring

end
end Yau.Target

end OAI
