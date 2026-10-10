import OAI.Geometry.NodalSets.Charts.LocalMetricJetContinuityLemmas
import OAI.Geometry.NodalSets.Persistence.LocalAdmissibilityPersistence

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

abbrev MetricJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)

def jetGradient (f : E → ℝ) (j : MetricJet E) (x : E) : E :=
  ContinuousLinearMap.inverse j.1 (fderiv ℝ f x)

def jetHessian (f : E → ℝ) (j : MetricJet E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x -
    (ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ f x)).comp (metricConnection j.1 j.2)

def JetAdmissible (f : E → ℝ) (j : MetricJet E) (x : E) : Prop :=
  let p := jetGradient f j x
  let H := jetHessian f j x
  p ≠ 0 ∧ ∃ t : E, j.1 p t = 0 ∧ j.1 t t = 1 ∧
    0 < H p p + (j.1 p p+4)*H t t

lemma jetGradient_continuousAt (f : E → ℝ) (j : MetricJet E) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hp : ∀ v, v ≠ 0 → 0 < j.1 v v) :
    ContinuousAt (fun z : MetricJet E × E ↦ jetGradient f z.1 z.2) (j,x) := by
  exact (metric_inverse_continuousAt (fun z : MetricJet E × E ↦ z.1.1) (j,x)
    (continuousAt_fst.fst) hp).clm_apply
      ((hf.continuousAt_fderiv (by simp)).comp continuousAt_snd)

lemma jetHessian_continuousAt (f : E → ℝ) (j : MetricJet E) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hp : ∀ v, v ≠ 0 → 0 < j.1 v v) :
    ContinuousAt (fun z : MetricJet E × E ↦ jetHessian f z.1 z.2) (j,x) := by
  have hD := (hf.continuousAt_fderiv (by simp)).comp (continuousAt_snd (p := (j,x)))
  exact (((hf.fderiv_right (m := ∞) (by simp)).continuousAt_fderiv (by simp)).comp
    continuousAt_snd).sub
    (((ContinuousLinearMap.compL ℝ E E ℝ).continuous.continuousAt.comp hD).clm_comp
      (metric_connection_continuousAt (fun z : MetricJet E × E ↦ z.1.1)
        (fun z ↦ z.1.2) (j,x) continuousAt_fst.fst continuousAt_fst.snd hp))

theorem jetAdmissible_eventually (f : E → ℝ) (j : MetricJet E) (x : E)
    (hf : ContDiffAt ℝ ∞ f x) (hp : ∀ v, v ≠ 0 → 0 < j.1 v v)
    (ha : JetAdmissible f j x) :
    ∀ᶠ z : MetricJet E × E in 𝓝 (j,x), JetAdmissible f z.1 z.2 := by
  obtain ⟨hp0,t,hpt,htt,hs⟩ := ha
  exact admissibility_eventually (fun z : MetricJet E × E ↦ z.1.1)
    (fun z ↦ jetHessian f z.1 z.2) (fun z ↦ jetGradient f z.1 z.2) (j,x)
    continuousAt_fst.fst (jetHessian_continuousAt f j x hf hp)
    (jetGradient_continuousAt f j x hf hp) (hp _ hp0) t hpt htt hs

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma jetAdmissible_actual (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : E) :
    JetAdmissible f (g x,fderiv ℝ g x) x ↔
      localMetricGradient g f x ≠ 0 ∧ ∃ t : E,
        g x (localMetricGradient g f x) t = 0 ∧ g x t t = 1 ∧
        0 < localMetricHessian g f x (localMetricGradient g f x) (localMetricGradient g f x) +
          (g x (localMetricGradient g f x) (localMetricGradient g f x)+4)*
            localMetricHessian g f x t t := Iff.rfl

end
end Yau.Geometry

end OAI
