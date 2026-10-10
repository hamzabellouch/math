import OAI.Geometry.NodalSets.Charts.CenteredSphereMetricLemmas
import OAI.Geometry.NodalSets.Charts.SphereChartArbitrarySecond

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff RealInnerProductSpace
noncomputable section

lemma sphereInverse_contDiff (p : Base) :
    ContDiff ℝ ∞ ((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm) := by
  rw [centeredSphereChart_inverse]
  exact contDiff_stereoInvFunAux.comp (centeredSphereIsometry p).contDiff

lemma sphere_restriction_chart_first_at (f : AmbientBase → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : Base) (y v : BaseModel) :
    fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm) y v =
      fderiv ℝ f ((extChartAt (𝓡 4) p).symm y : AmbientBase) (sphereChartDerivative p y v) := by
  change fderiv ℝ (f ∘ ((Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm)) y v = _
  rw [fderiv_comp y (hf.differentiable (by simp) _)
    ((sphereInverse_contDiff p).differentiable (by simp) _),
    ← sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)]
  rfl

lemma smooth_comp_second_at {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (f : F → G) (h : E → F) (hf : ContDiff ℝ ∞ f) (hh : ContDiff ℝ ∞ h)
    (x u v : E) :
    fderiv ℝ (fderiv ℝ (f ∘ h)) x u v =
      fderiv ℝ (fderiv ℝ f) (h x) (fderiv ℝ h x u) (fderiv ℝ h x v) +
      fderiv ℝ f (h x) (fderiv ℝ (fderiv ℝ h) x u v) := by
  have hdf := (hf.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiable (by simp)
  have hdh := (hh.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiable (by simp)
  have hG := (hdf (h x)).hasFDerivAt.comp x (hh.differentiable (by simp) x).hasFDerivAt
  have hD := (hdh x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hd := hG.clm_apply hD
  have he : (fun z ↦ fderiv ℝ (f ∘ h) z v) =
      (fun z ↦ fderiv ℝ f (h z) (fderiv ℝ h z v)) := by
    funext z
    rw [fderiv_comp z (hf.differentiable (by simp) _) (hh.differentiable (by simp) _)]
    rfl
  have hQ := ((hf.comp hh).fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiable (by simp) x
  have hE := congrArg (fun L : E →L[ℝ] G ↦ L u)
    (hQ.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).fderiv
  simp only [ContinuousLinearMap.comp_zero,zero_add,ContinuousLinearMap.flip_apply] at hE
  change HasFDerivAt (fun z ↦ fderiv ℝ f (h z) (fderiv ℝ h z v)) _ x at hd
  rw [← hE,he,hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_zero,
    zero_add,ContinuousLinearMap.flip_apply]
  exact add_comm _ _

lemma sphere_restriction_chart_second_at (f : AmbientBase → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : Base) (y u v : BaseModel) :
    fderiv ℝ (fderiv ℝ ((fun x : Base ↦ f x) ∘ (extChartAt (𝓡 4) p).symm)) y u v =
      fderiv ℝ (fderiv ℝ f) ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        (sphereChartDerivative p y u) (sphereChartDerivative p y v) +
      fderiv ℝ f ((extChartAt (𝓡 4) p).symm y : AmbientBase)
        (fderiv ℝ (sphereChartDerivative p) y u v) := by
  let F : BaseModel → AmbientBase := (Subtype.val : Base → AmbientBase) ∘ (extChartAt (𝓡 4) p).symm
  have hFd : fderiv ℝ F = sphereChartDerivative p := by
    funext z
    exact (sphereChartDerivative_eq_fderiv p (by rw [centeredSphereChart_target]; trivial)).symm
  have h := smooth_comp_second_at f F hf (sphereInverse_contDiff p) y u v
  rw [hFd] at h
  exact h

end
end Yau.Target

end OAI
