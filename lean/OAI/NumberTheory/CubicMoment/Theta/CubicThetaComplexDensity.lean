import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegral

namespace OAI

/-! The complex-valued coordinate integral has the same literal
hyperbolic density v^-3 as the real energy integral. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointIntegral_complex_coordinates {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℂ) :
    (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ y in cubicThetaPointCoordinates '' S, f y ∂cubicThetaHyperbolicMeasure := by
  rw [← cubicThetaPointCoordinates_map_restrict hS]
  exact (cubicThetaPointInclusion_measurableEmbedding.integral_map f).symm

lemma cubicThetaPointIntegral_complex_density {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) (f : ℂ × ℝ → ℂ) :
    (∫ p in S, f (cubicThetaPointCoordinates p) ∂cubicThetaPointMeasure)=
      ∫ y in cubicThetaPointCoordinates '' S, f y/(y.2:ℂ)^3 := by
  rw [cubicThetaPointIntegral_complex_coordinates hS]
  have hT := cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS
  rw [cubicThetaHyperbolicMeasure,setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    cubicThetaHyperbolicDensity_measurable.aemeasurable
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ hT]
  apply setIntegral_congr_fun hT
  rintro y ⟨p,hp,rfl⟩
  have hv : 0<(cubicThetaPointCoordinates p).2 := p.property
  simp only [cubicThetaHyperbolicDensity,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_nonneg hv.le 3)),Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_pow,div_eq_mul_inv]
  ring

end CubicFirstMoment

end

end OAI
