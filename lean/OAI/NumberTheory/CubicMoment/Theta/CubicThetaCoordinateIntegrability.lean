import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateIntegral

namespace OAI

/-! Integrability in the actual positive-height coordinates retains
the precise hyperbolic density v^-3. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointIntegrable_density {S : Set CubicThetaPoint} (hS : MeasurableSet S)
    (f : ℂ × ℝ → ℝ) :
    IntegrableOn (fun p => f (cubicThetaPointCoordinates p)) S cubicThetaPointMeasure ↔
      IntegrableOn (fun y => f y/y.2^3) (cubicThetaPointCoordinates '' S) := by
  have hT := cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS
  have hc := (cubicThetaPointInclusion_measurableEmbedding.integrable_map_iff
    (μ:=cubicThetaPointMeasure.restrict S) (g:=f)).symm
  rw [cubicThetaPointCoordinates_map_restrict hS] at hc
  change IntegrableOn (fun p => f (cubicThetaPointCoordinates p)) S cubicThetaPointMeasure ↔ _ at hc
  rw [hc]
  unfold IntegrableOn cubicThetaHyperbolicMeasure
  rw [restrict_withDensity hT,integrable_withDensity_iff_integrable_smul'
    cubicThetaHyperbolicDensity_measurable (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))]
  apply integrable_congr
  filter_upwards [ae_restrict_mem hT] with y hy
  obtain ⟨p,hp,rfl⟩ := hy
  have hv : 0<(cubicThetaPointCoordinates p).2 := p.property
  rw [cubicThetaHyperbolicDensity,ENNReal.toReal_ofReal
    (inv_nonneg.mpr (pow_nonneg hv.le 3))]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

end CubicFirstMoment

end

end OAI
