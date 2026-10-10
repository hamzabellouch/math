import OAI.Geometry.NodalSets.Charts.LocalMetricJetContinuityLemmas

namespace OAI

namespace Yau.Geometry
open Filter
open scoped ContDiff Topology
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma linearScalar_second (e : F ≃L[ℝ] E) (f : E → ℝ) (x : F)
    (hf : ContDiffAt ℝ ∞ f (e x)) (u v : F) :
    fderiv ℝ (fderiv ℝ (f ∘ e)) x u v =
      fderiv ℝ (fderiv ℝ f) (e x) (e u) (e v) := by
  have hnear := ((hf.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by simp)).filter_mono
    e.continuous.continuousAt.tendsto
  have he : fderiv ℝ (f ∘ e) =ᶠ[𝓝 x]
      (fun y ↦ linearCovectorPull e (fderiv ℝ f (e y))) := by
    filter_upwards [hnear] with y hy
    change ContDiffAt ℝ 1 f (e y) at hy
    exact linearScalar_fderiv e f y (hy.differentiableAt (by simp))
  have hd := (hf.fderiv_right (show (∞ : WithTop ℕ∞)+1 ≤ ∞ by simp)).differentiableAt (by simp)
  have ht := (linearCovectorPull e).toContinuousLinearMap.hasFDerivAt.comp x
    (hd.hasFDerivAt.comp x e.hasFDerivAt)
  change HasFDerivAt (fun y ↦ linearCovectorPull e (fderiv ℝ f (e y))) _ x at ht
  rw [he.fderiv_eq]
  rw [ht.fderiv]
  rfl

lemma linearMetricField_hessian (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) (hg : DifferentiableAt ℝ g (e x))
    (hf : ContDiffAt ℝ ∞ f (e x)) (u v : F) :
    localMetricHessian (linearMetricField e g) (f ∘ e) x u v =
      localMetricHessian g f (e x) (e u) (e v) := by
  change fderiv ℝ (fderiv ℝ (f ∘ e)) x u v -
    fderiv ℝ (f ∘ e) x (metricConnection _ _ u v) = _
  rw [linearScalar_second e f x hf,linearMetricField_connection e g x hp hg,
    linearScalar_fderiv e f x (hf.differentiableAt (by simp)),linearCovectorPull_apply,
    e.apply_symm_apply]
  rfl

theorem linearMetricField_admissible (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) (hg : DifferentiableAt ℝ g (e x))
    (hf : ContDiffAt ℝ ∞ f (e x))
    (hn : localMetricGradient g f (e x) ≠ 0)
    (ha : ∃ t : E, g (e x) (localMetricGradient g f (e x)) t = 0 ∧
      g (e x) t t = 1 ∧
      0 < localMetricHessian g f (e x) (localMetricGradient g f (e x)) (localMetricGradient g f (e x)) +
        (g (e x) (localMetricGradient g f (e x)) (localMetricGradient g f (e x))+4) *
          localMetricHessian g f (e x) t t) :
    let G := linearMetricField e g
    let P := localMetricGradient G (f ∘ e) x
    let H := localMetricHessian G (f ∘ e) x
    P ≠ 0 ∧ ∃ t : F, G x P t = 0 ∧ G x t t = 1 ∧
      0 < H P P + (G x P P+4)*H t t := by
  dsimp only
  rw [linearMetricField_gradient e g f x hp (hf.differentiableAt (by simp))]
  refine ⟨?_,?_⟩
  · intro h
    exact hn (by simpa using congrArg e h)
  · obtain ⟨t,ht,hu,hs⟩ := ha
    refine ⟨e.symm t,?_,?_,?_⟩
    · simpa only [linearMetricField,linearMetricPull_apply,e.apply_symm_apply] using ht
    · simpa only [linearMetricField,linearMetricPull_apply,e.apply_symm_apply] using hu
    · simpa only [linearMetricField_hessian e g f x hp hg hf,
        linearMetricField,linearMetricPull_apply,e.apply_symm_apply] using hs

end
end Yau.Geometry

end OAI
