import OAI.Geometry.NodalSets.Charts.SeedMetricNeighborhood
import OAI.Geometry.NodalSets.Charts.SphereChartVolume
import OAI.Geometry.NodalSets.Coefficients.CoefficientMetricJets

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff RealInnerProductSpace
noncomputable section

def roundCoefficients (y : BaseModel) : CoefficientPoint BaseModel :=
  (ContinuousLinearMap.inverse (roundChartMetric seedPoint y),1)

def roundCoefficientJet (y : BaseModel) : CoefficientFirstJet BaseModel :=
  (roundCoefficients y,fderiv ℝ roundCoefficients y)

lemma roundChartMetric_positive (y : BaseModel) (v : BaseModel) (hv : v ≠ 0) :
    0 < roundChartMetric seedPoint y v v := by
  rw [roundChartMetric_apply]
  apply real_inner_self_pos.mpr
  intro he
  apply hv
  apply sphereChartDerivative_injective seedPoint (by rw [centeredSphereChart_target]; trivial)
  simpa using he

lemma roundCoefficient_inverse (y : BaseModel) :
    (positiveMetricEquiv (roundChartMetric seedPoint y) (roundChartMetric_positive y)).symm.toContinuousLinearMap =
      (roundCoefficients y).1 :=
  (ContinuousLinearMap.inverse_equiv (positiveMetricEquiv _ (roundChartMetric_positive y))).symm

lemma roundCoefficients_smooth : ContDiff ℝ ∞ roundCoefficients := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (roundChartMetric seedPoint y) := by
    exact contDiffAt_map_inverse (positiveMetricEquiv _ (roundChartMetric_positive y))
  exact (hi.comp y (roundChartMetric_smooth seedPoint).contDiffAt).prodMk contDiffAt_const

lemma roundCoefficients_metric (y : BaseModel) :
    coefficientMetricValue (roundCoefficients y) = roundChartMetric seedPoint y := by
  simp only [coefficientMetricValue,roundCoefficients,one_smul]
  have h1 : ContinuousLinearMap.inverse (roundChartMetric seedPoint y) =
      (positiveMetricEquiv _ (roundChartMetric_positive y)).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv _ (roundChartMetric_positive y))
  rw [h1,ContinuousLinearMap.inverse_equiv]
  rfl

lemma roundCoefficientJet_metric (y : BaseModel) :
    coefficientMetricJet (roundCoefficientJet y) = roundMetricJet y := by
  rw [roundCoefficientJet,coefficientMetricJet_actual roundCoefficients y
    (roundCoefficients_smooth.differentiable (by simp) y)
    (positiveMetricEquiv _ (roundChartMetric_positive y)).symm (roundCoefficient_inverse y)]
  have he : coefficientMetricValue ∘ roundCoefficients = roundChartMetric seedPoint :=
    funext roundCoefficients_metric
  rw [he,roundCoefficients_metric]
  rfl

lemma roundCoefficientJet_continuous : Continuous roundCoefficientJet :=
  roundCoefficients_smooth.continuous.prodMk (roundCoefficients_smooth.continuous_fderiv (by simp))

end
end Yau.Target

end OAI
