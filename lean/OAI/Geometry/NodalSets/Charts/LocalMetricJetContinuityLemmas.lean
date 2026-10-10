import OAI.Geometry.NodalSets.Charts.LocalMetricJets

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

lemma metric_inverse_continuousAt {T : Type*} [TopologicalSpace T]
    (g : T → E →L[ℝ] E →L[ℝ] ℝ) (x : T) (hg : ContinuousAt g x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContinuousAt (fun y ↦ ContinuousLinearMap.inverse (g y)) x := by
  have hc := (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (positiveMetricEquiv (g x) hp)).continuousAt
  have hc' : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (g x) := by
    convert hc using 1
    rfl
  exact hc'.comp hg

lemma metric_connection_continuousAt {T : Type*} [TopologicalSpace T]
    (g : T → E →L[ℝ] E →L[ℝ] ℝ) (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (x : T) (hg : ContinuousAt g x) (hD : ContinuousAt D x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) :
    ContinuousAt (fun y ↦ metricConnection (g y) (D y)) x := by
  have hflip : ContinuousAt (fun t ↦ (D t).flip) x :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.continuousAt.comp hD
  have hcov : ContinuousAt (fun t ↦ christoffelCovector (D t)) x :=
    ((hD.add hflip).sub
      ((continuousAt_const (y := (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).clm_comp hflip)).const_smul (1/2:ℝ)
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).continuous.continuousAt.comp
    (metric_inverse_continuousAt g x hg hp)).clm_comp hcov

lemma localMetricGradient_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hg : ContinuousAt g x) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) : ContinuousAt (localMetricGradient g f) x :=
  (metric_inverse_continuousAt g x hg hp).clm_apply (hf.continuousAt_fderiv (by simp))

lemma localMetricHessian_continuousAt (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hg : ContDiffAt ℝ ∞ g x) (hf : ContDiffAt ℝ ∞ f x)
    (hp : ∀ v, v ≠ 0 → 0 < g x v v) : ContinuousAt (localMetricHessian g f) x := by
  have hD := hf.continuousAt_fderiv (by simp)
  exact ((hf.fderiv_right (m := ∞) (by simp)).continuousAt_fderiv (by simp)).sub
    (((ContinuousLinearMap.compL ℝ E E ℝ).continuous.continuousAt.comp hD).clm_comp
      (metric_connection_continuousAt g (fderiv ℝ g) x hg.continuousAt
        (hg.continuousAt_fderiv (by simp)) hp))

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def linearCovectorPull (e : F ≃L[ℝ] E) : (E →L[ℝ] ℝ) ≃L[ℝ] (F →L[ℝ] ℝ) :=
  e.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

def linearMetricPull (e : F ≃L[ℝ] E) :
    (E →L[ℝ] E →L[ℝ] ℝ) ≃L[ℝ] (F →L[ℝ] F →L[ℝ] ℝ) :=
  e.symm.arrowCongr (linearCovectorPull e)

lemma linearCovectorPull_apply (e : F ≃L[ℝ] E) (α : E →L[ℝ] ℝ) (u : F) :
    linearCovectorPull e α u = α (e u) := rfl

lemma linearMetricPull_apply (e : F ≃L[ℝ] E) (g : E →L[ℝ] E →L[ℝ] ℝ) (u v : F) :
    linearMetricPull e g u v = g (e u) (e v) := rfl

def linearMetricField (e : F ≃L[ℝ] E) (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (x : F) : F →L[ℝ] F →L[ℝ] ℝ := linearMetricPull e (g (e x))

lemma linearMetricField_positive (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) :
    ∀ v, v ≠ 0 → 0 < linearMetricField e g x v v := by
  intro v hv
  exact hp (e v) (by intro h; exact hv (e.injective (h.trans e.map_zero.symm)))

lemma linearMetricField_fderiv (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F) (hg : DifferentiableAt ℝ g (e x)) :
    fderiv ℝ (linearMetricField e g) x =
      (linearMetricPull e).toContinuousLinearMap ∘L (fderiv ℝ g (e x)) ∘L e.toContinuousLinearMap := by
  exact ((linearMetricPull e).toContinuousLinearMap.hasFDerivAt.comp x
    (hg.hasFDerivAt.comp x e.hasFDerivAt)).fderiv

lemma linearMetricField_fderiv_apply (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F) (hg : DifferentiableAt ℝ g (e x)) (u v w : F) :
    fderiv ℝ (linearMetricField e g) x u v w = fderiv ℝ g (e x) (e u) (e v) (e w) := by
  rw [linearMetricField_fderiv e g x hg]; rfl

lemma linearScalar_fderiv (e : F ≃L[ℝ] E) (f : E → ℝ) (x : F)
    (hf : DifferentiableAt ℝ f (e x)) :
    fderiv ℝ (f ∘ e) x = linearCovectorPull e (fderiv ℝ f (e x)) := by
  exact (hf.hasFDerivAt.comp x e.hasFDerivAt).fderiv

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

lemma localMetricGradient_pair (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (f : E → ℝ) (x : E) (hp : ∀ v, v ≠ 0 → 0 < g x v v) (v : E) :
    g x (localMetricGradient g f x) v = fderiv ℝ f x v := by
  have hi : ContinuousLinearMap.inverse (g x) =
      (positiveMetricEquiv (g x) hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv (g x) hp)
  unfold localMetricGradient
  rw [hi]
  exact congrArg (fun α : E →L[ℝ] ℝ ↦ α v)
    ((positiveMetricEquiv (g x) hp).apply_symm_apply (fderiv ℝ f x))

lemma linearMetricField_gradient (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (f : E → ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) (hf : DifferentiableAt ℝ f (e x)) :
    localMetricGradient (linearMetricField e g) (f ∘ e) x =
      e.symm (localMetricGradient g f (e x)) := by
  apply localMetricGradient_eq_of_pair _ _ _ _ (linearMetricField_positive e g x hp)
  intro v
  change g (e x) (e (e.symm (localMetricGradient g f (e x)))) (e v) = _
  rw [e.apply_symm_apply,localMetricGradient_pair g f (e x) hp,
    linearScalar_fderiv e f x hf]
  rfl

lemma metricConnection_pair (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v, v ≠ 0 → 0 < g v v) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (u v w : E) :
    g (metricConnection g D u v) w = (D u v w + D v u w - D w u v)/2 := by
  rw [metricConnection_eq g hp D]
  exact christoffelTensor_pair (positiveMetricEquiv g hp) D u v w

lemma linearMetricField_connection (e : F ≃L[ℝ] E)
    (g : E → E →L[ℝ] E →L[ℝ] ℝ) (x : F)
    (hp : ∀ v, v ≠ 0 → 0 < g (e x) v v) (hg : DifferentiableAt ℝ g (e x)) (u v : F) :
    metricConnection (linearMetricField e g x) (fderiv ℝ (linearMetricField e g) x) u v =
      e.symm (metricConnection (g (e x)) (fderiv ℝ g (e x)) (e u) (e v)) := by
  apply (positiveMetricEquiv _ (linearMetricField_positive e g x hp)).injective
  ext w
  change linearMetricField e g x _ w = linearMetricField e g x _ w
  rw [metricConnection_pair _ (linearMetricField_positive e g x hp)]
  change _ = g (e x) (e (e.symm _)) (e w)
  rw [e.apply_symm_apply,metricConnection_pair _ hp]
  simp only [linearMetricField_fderiv_apply e g x hg]

end Yau.Geometry

end

end OAI
