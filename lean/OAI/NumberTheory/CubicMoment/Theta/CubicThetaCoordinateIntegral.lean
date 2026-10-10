import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! Restricted coordinate integration for the actual hyperbolic measure.
This identifies the v^-3 density appearing in the local energy graph. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointCoordinates_map_restrict {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) :
    (cubicThetaPointMeasure.restrict S).map cubicThetaPointCoordinates=
      cubicThetaHyperbolicMeasure.restrict (cubicThetaPointCoordinates '' S) := by
  ext B hB
  rw [Measure.map_apply cubicThetaPointInclusion_measurableEmbedding.measurable hB,
    Measure.restrict_apply (hB.preimage cubicThetaPointInclusion_measurableEmbedding.measurable),
    cubicThetaPointMeasure_apply ((hB.preimage
      cubicThetaPointInclusion_measurableEmbedding.measurable).inter hS),
    Measure.restrict_apply hB,Set.image_preimage_inter]

lemma cubicThetaPointIntegral_coordinates {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℝ) :
    (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ y in cubicThetaPointCoordinates '' S, f y ∂cubicThetaHyperbolicMeasure := by
  rw [← cubicThetaPointCoordinates_map_restrict hS]
  exact (cubicThetaPointInclusion_measurableEmbedding.integral_map f).symm

lemma cubicThetaHyperbolicDensity_measurable : Measurable cubicThetaHyperbolicDensity :=
  ((measurable_snd.pow_const 3).inv).ennreal_ofReal

lemma cubicThetaPointIntegral_density {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℝ) :
    (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ y in cubicThetaPointCoordinates '' S, f y/y.2^3 := by
  rw [cubicThetaPointIntegral_coordinates hS]
  have hT := cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS
  rw [cubicThetaHyperbolicMeasure,setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    cubicThetaHyperbolicDensity_measurable.aemeasurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ hT]
  apply setIntegral_congr_fun hT
  rintro y ⟨p,hp,rfl⟩
  have hv : 0<(cubicThetaPointCoordinates p).2 := p.property
  simp only [cubicThetaHyperbolicDensity,ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hv.le 3)),
    smul_eq_mul,div_eq_mul_inv]
  ring

end CubicFirstMoment

end

end OAI
