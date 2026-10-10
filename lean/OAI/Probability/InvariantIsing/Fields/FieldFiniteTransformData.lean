import OAI.Probability.InvariantIsing.Fields.FieldFiniteCoordinateAverage

namespace OAI

/-! The explicit joint gradient and Hessian of one finite-height Gaussian
recursion step. All expressions use the same normalized Gaussian law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldFiniteFamily

variable {n : ℕ} {I : Set (Fin n → ℝ)} (F : FieldFiniteFamily n I)

def mean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (p : FieldCovariate n) : ℝ :=
  ∫ u, F.shiftedMean a v u p ∂F.affineLaw a v ζ p

def tangent (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n) (p : FieldCovariate n) : ℝ :=
  ∫ u, F.shiftedTangent a v i u p ∂F.affineLaw a v ζ p

def curvature (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (p : FieldCovariate n) : ℝ :=
  (∫ u, F.XX (F.shiftPoint a v u p) ∂F.affineLaw a v ζ p) + ζ *
    ((∫ u, F.shiftedMean a v u p * F.shiftedMean a v u p ∂F.affineLaw a v ζ p) -
      F.mean a v ζ p * F.mean a v ζ p)

def mixedMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n) (p : FieldCovariate n) : ℝ :=
  (∫ u, F.shiftedMixed a v i u p ∂F.affineLaw a v ζ p) + ζ *
    ((∫ u, F.shiftedMean a v u p * F.shiftedTangent a v i u p ∂F.affineLaw a v ζ p) -
      F.mean a v ζ p * F.tangent a v ζ i p)

def secondMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i j : Fin n) (p : FieldCovariate n) : ℝ :=
  (∫ u, F.shiftedHessian a v i j u p ∂F.affineLaw a v ζ p) + ζ *
    ((∫ u, F.shiftedTangent a v i u p * F.shiftedTangent a v j u p ∂F.affineLaw a v ζ p) -
      F.tangent a v ζ i p * F.tangent a v ζ j p)

lemma secondMean_symmetric (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i j : Fin n)
    {p : FieldCovariate n} (hp : p.1 ∈ I) :
    F.secondMean a v ζ i j p = F.secondMean a v ζ j i p := by
  have hH : (∫ u, F.shiftedHessian a v i j u p ∂F.affineLaw a v ζ p) =
      ∫ u, F.shiftedHessian a v j i u p ∂F.affineLaw a v ζ p :=
    integral_congr_ae (ae_of_all _ fun u => F.shiftedHessian_symmetric a v i j u hp)
  have hT : (∫ u, F.shiftedTangent a v i u p * F.shiftedTangent a v j u p
      ∂F.affineLaw a v ζ p) = ∫ u, F.shiftedTangent a v j u p * F.shiftedTangent a v i u p
      ∂F.affineLaw a v ζ p := integral_congr_ae (ae_of_all _ fun u => mul_comm _ _)
  unfold secondMean
  rw [hH, hT, mul_comm (F.tangent a v ζ i p) (F.tangent a v ζ j p)]

lemma measurable_mean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) : Measurable (F.mean a v ζ) :=
  F.measurable_affine_average a v ζ (F.joint_measurable_shiftedMean a v)

lemma measurable_tangent (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n) :
    Measurable (F.tangent a v ζ i) :=
  F.measurable_affine_average a v ζ (F.joint_measurable_shiftedTangent a v i)

lemma measurable_curvature (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) :
    Measurable (F.curvature a v ζ) := by
  exact (F.measurable_affine_average a v ζ (F.mXX.comp (by dsimp only [shiftPoint, fieldFiniteVariance]; fun_prop))).add
    (((F.measurable_affine_average a v ζ ((F.joint_measurable_shiftedMean a v).mul
      (F.joint_measurable_shiftedMean a v))).sub
      ((F.measurable_mean a v ζ).mul (F.measurable_mean a v ζ))).const_mul ζ)

lemma measurable_mixedMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i : Fin n) :
    Measurable (F.mixedMean a v ζ i) := by
  exact (F.measurable_affine_average a v ζ (F.joint_measurable_shiftedMixed a v i)).add
    (((F.measurable_affine_average a v ζ ((F.joint_measurable_shiftedMean a v).mul
      (F.joint_measurable_shiftedTangent a v i))).sub
      ((F.measurable_mean a v ζ).mul (F.measurable_tangent a v ζ i))).const_mul ζ)

lemma measurable_secondMean (a : ℝ) (v : Fin n → ℝ) (ζ : ℝ) (i j : Fin n) :
    Measurable (F.secondMean a v ζ i j) := by
  exact (F.measurable_affine_average a v ζ (F.joint_measurable_shiftedHessian a v i j)).add
    (((F.measurable_affine_average a v ζ ((F.joint_measurable_shiftedTangent a v i).mul
      (F.joint_measurable_shiftedTangent a v j))).sub
      ((F.measurable_tangent a v ζ i).mul (F.measurable_tangent a v ζ j))).const_mul ζ)

end FieldFiniteFamily
end InvariantIsing

end

end OAI
