import OAI.Geometry.NodalSets.Charts.MetricConnectionFamilyLemmas

namespace OAI

namespace Yau.Geometry
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def localMetricGradient (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : E) : E :=
  ContinuousLinearMap.inverse (g x) (fderiv ℝ f x)

def localMetricHessian (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x -
    (ContinuousLinearMap.compL ℝ E E ℝ (fderiv ℝ f x)).comp
      (metricConnection (g x) (fderiv ℝ g x))

lemma localMetricGradient_eq_of_pair [FiniteDimensional ℝ E] (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x p : E) (hp : ∀ v, v ≠ 0 → 0 < g x v v)
    (he : ∀ v, g x p v = fderiv ℝ f x v) : localMetricGradient g f x = p := by
  have hmap : g x p = fderiv ℝ f x := by ext v; exact he v
  unfold localMetricGradient
  have hi : ContinuousLinearMap.inverse (g x) =
      (positiveMetricEquiv (g x) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g x) hp)
  rw [← hmap,hi]
  exact (positiveMetricEquiv (g x) hp).symm_apply_apply p

lemma localMetricHessian_of_connection_zero (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (h : metricConnection (g x) (fderiv ℝ g x) = 0) :
    localMetricHessian g f x = fderiv ℝ (fderiv ℝ f) x := by
  simp [localMetricHessian,h]

end
end Yau.Geometry

end OAI
