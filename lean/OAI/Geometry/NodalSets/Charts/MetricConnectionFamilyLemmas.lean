import OAI.Geometry.NodalSets.Charts.PositiveMetric

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

def metricConnection (g : E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E (ContinuousLinearMap.inverse g)).comp
    (christoffelCovector D)

omit [CompleteSpace E] in
lemma metricConnection_eq (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :
    metricConnection g D = christoffelTensor (positiveMetricEquiv g hp) D := by
  have hi : ContinuousLinearMap.inverse g = (positiveMetricEquiv g hp).symm.toContinuousLinearMap :=
    ContinuousLinearMap.inverse_equiv (positiveMetricEquiv g hp)
  simp only [metricConnection, christoffelTensor, hi]

variable {T : Type*} [TopologicalSpace T]
lemma positive_metric_inverse_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g)
    (hp : ∀ t, ∀ v : E, v ≠ 0 → 0 < g t v v) :
    Continuous (fun t ↦ ContinuousLinearMap.inverse (g t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (contDiffAt_map_inverse (n := (1:ℕ∞ω)) (positiveMetricEquiv (g t) (hp t))).continuousAt
  have hc' : ContinuousAt
      (ContinuousLinearMap.inverse : (E →L[ℝ] E →L[ℝ] ℝ) → ((E →L[ℝ] ℝ) →L[ℝ] E)) (g t) := by
    convert hc using 1
    rfl
  exact hc'.comp hg.continuousAt

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma christoffelCovector_continuous (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    (hD : Continuous D) : Continuous (fun t ↦ christoffelCovector (D t)) := by
  have hflip : Continuous (fun t ↦ (D t).flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E (E →L[ℝ] ℝ)).continuous.comp hD
  exact ((hD.add hflip).sub (hflip.const_clm_comp
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap)).const_smul (1/2:ℝ)

theorem metricConnection_continuous (g : T → E →L[ℝ] E →L[ℝ] ℝ)
    (D : T → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hg : Continuous g) (hD : Continuous D)
    (hp : ∀ t, ∀ v : E, v ≠ 0 → 0 < g t v v) :
    Continuous (fun t ↦ metricConnection (g t) (D t)) := by
  exact ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E).continuous.comp
    (positive_metric_inverse_continuous g hg hp)).clm_comp (christoffelCovector_continuous D hD)

theorem smooth_metric_connection_continuous (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ y, ∀ v : E, v ≠ 0 → 0 < g y v v) :
    Continuous (fun y ↦ metricConnection (g y) (fderiv ℝ g y)) := by
  exact metricConnection_continuous g (fderiv ℝ g) hg.continuous
    (hg.continuous_fderiv (by simp)) hp

end

open scoped ContDiff
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma metric_derivative_symmetric (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (y : E) (hg : HasFDerivAt g D y)
    (hs : ∀ x u v, g x u v = g x v u) : ∀ w u v, D w u v = D w v u := by
  intro w u v
  have huv := (hg.clm_apply (hasFDerivAt_const u y)).clm_apply (hasFDerivAt_const v y)
  have hvu := (hg.clm_apply (hasFDerivAt_const v y)).clm_apply (hasFDerivAt_const u y)
  have he : (fun x ↦ g x u v) = fun x ↦ g x v u := funext (fun x ↦ hs x u v)
  have hh := congrArg (fun f : E → ℝ ↦ fderiv ℝ f y w) he
  rw [huv.fderiv, hvu.fderiv] at hh
  simpa using hh

theorem exists_normal_chart (g : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (y : E) (hp : ∀ v : E, v ≠ 0 → 0 < g y v v) :
    ∃ F : OpenPartialHomeomorph E E,
      0 ∈ F.source ∧ F 0 = y ∧ ContDiff ℝ ∞ (F : E → E) ∧
      ContDiffAt ℝ ∞ F.symm y ∧
      fderiv ℝ (F : E → E) 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ u v, pullbackMetric g F 0 u v = g y u v) ∧
      ∀ u v, fderiv ℝ (fun x ↦ pullbackMetric g F x u v) 0 = 0 := by
  have hd := (hg.differentiable (by simp)).differentiableAt.hasFDerivAt (x := y)
  obtain ⟨B, hB, hc⟩ := positive_metric_connection (g y) hp (hs y) (fderiv ℝ g y)
    (metric_derivative_symmetric g (fderiv ℝ g y) y hd hs)
  let e := ContinuousLinearEquiv.refl ℝ E
  refine ⟨quadraticChart y e B, quadraticChart_source y e B,
    quadraticChartMap_zero y e B, quadraticChartMap_smooth y e B,
    quadraticChart_inverse_smooth y e B, (quadraticChartMap_deriv_zero y e B).fderiv,
    ?_, ?_⟩
  · intro u v
    exact pullbackMetric_quadratic_zero g y e B u v
  · intro u v
    exact quadratic_chart_metric_first_zero g (fderiv ℝ g y) y hd e B hB hc u v

end Yau.Geometry

end

end OAI
