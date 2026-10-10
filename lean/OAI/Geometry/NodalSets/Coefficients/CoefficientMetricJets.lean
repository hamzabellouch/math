import OAI.Geometry.NodalSets.Charts.MetricJetAdmissibility

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev CoefficientPoint (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ((E →L[ℝ] ℝ) →L[ℝ] E) × ℝ

abbrev CoefficientDerivative (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  letI : TopologicalSpace (CoefficientPoint E) :=
    (inferInstance : NormedAddCommGroup (CoefficientPoint E)).toUniformSpace.toTopologicalSpace
  letI : AddCommMonoid (CoefficientPoint E) :=
    (inferInstance : NormedAddCommGroup (CoefficientPoint E)).toAddCommMonoid
  letI : Module ℝ (CoefficientPoint E) :=
    (inferInstance : NormedSpace ℝ (CoefficientPoint E)).toModule
  E →L[ℝ] CoefficientPoint E

abbrev CoefficientFirstJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  CoefficientPoint E × CoefficientDerivative E

def coefficientMetricValue (c : CoefficientPoint E) : E →L[ℝ] E →L[ℝ] ℝ :=
  c.2 • ContinuousLinearMap.inverse c.1

def coefficientMetricJet (j : CoefficientFirstJet E) : MetricJet E :=
  (coefficientMetricValue j.1,(fderiv ℝ coefficientMetricValue j.1).comp j.2)

lemma coefficientMetricValue_smoothAt (c : CoefficientPoint E)
    (e : (E →L[ℝ] ℝ) ≃L[ℝ] E) (he : e.toContinuousLinearMap = c.1) :
    ContDiffAt ℝ ∞ (coefficientMetricValue : CoefficientPoint E → E →L[ℝ] E →L[ℝ] ℝ) c := by
  have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse c.1 := by
    rw [← he]; exact contDiffAt_map_inverse e
  exact contDiffAt_snd.smul (hi.comp c contDiffAt_fst)

lemma coefficientMetricJet_continuousAt (j : CoefficientFirstJet E)
    (e : (E →L[ℝ] ℝ) ≃L[ℝ] E) (he : e.toContinuousLinearMap = j.1.1) :
    ContinuousAt (coefficientMetricJet : CoefficientFirstJet E → MetricJet E) j := by
  have h := coefficientMetricValue_smoothAt j.1 e he
  exact (h.continuousAt.comp continuousAt_fst).prodMk
    (((h.continuousAt_fderiv (by simp)).comp continuousAt_fst).clm_comp continuousAt_snd)

lemma coefficientMetricJet_actual (c : E → CoefficientPoint E) (x : E)
    (hc : DifferentiableAt ℝ c x) (e : (E →L[ℝ] ℝ) ≃L[ℝ] E)
    (he : e.toContinuousLinearMap = (c x).1) :
    coefficientMetricJet (c x,fderiv ℝ c x) =
      (coefficientMetricValue (c x), fderiv ℝ (coefficientMetricValue ∘ c) x) := by
  apply Prod.ext
  · rfl
  · exact (fderiv_comp x ((coefficientMetricValue_smoothAt (c x) e he).differentiableAt (by simp)) hc).symm

end
end Yau.Geometry

end OAI
