import OAI.Analysis.Mahler.PullbackRegularity
import OAI.Analysis.Mahler.OrientedChartIntegral
import OAI.Analysis.Mahler.InteriorStokes

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MahlerStokes

/-- The oriented pullback, extended by zero outside the actual chart target. -/
def extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ :=
  e.target.indicator (fun y => jacobianOrientation (fderiv ℝ e.symm y).det •
    pullbackForm e.symm ω y)

 theorem chart_inverse_det_ne_zero {d : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (he : ∀ x ∈ e.source, DifferentiableAt ℝ e x)
    (hi : ∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) {y : Fin d → ℝ} (hy : y ∈ e.target) :
    (fderiv ℝ e.symm y).det ≠ 0 := by
  have hd := (he (e.symm y) (e.map_target hy)).hasFDerivAt.comp y (hi y hy).hasFDerivAt
  have hf : (fun z => e (e.symm z)) =ᶠ[𝓝 y] (fun z => z) := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  have hm : (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) =
      ContinuousLinearMap.id ℝ (Fin d → ℝ) :=
    (hd.congr_of_eventuallyEq hf.symm).unique (hasFDerivAt_id y)
  have hdet := congrArg ContinuousLinearMap.det hm
  change LinearMap.det ((fderiv ℝ e (e.symm y)).toLinearMap.comp
    (fderiv ℝ e.symm y).toLinearMap) = LinearMap.det (LinearMap.id :
      (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  intro hz
  change LinearMap.det (fderiv ℝ e.symm y).toLinearMap = 0 at hz
  rw [hz, mul_zero] at hdet
  exact zero_ne_one hdet

 theorem tsupport_extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ e.source) :
    tsupport (extendedChartForm e ω) ⊆ e '' tsupport ω := by
  have hK : IsCompact (e '' tsupport ω) := hc.image_of_continuousOn (e.continuousOn.mono hs)
  apply closure_minimal _ hK.isClosed
  intro y hy
  have hne : extendedChartForm e ω y ≠ 0 := hy
  have hyt : y ∈ e.target := by
    by_contra h
    exact hne (by simp [extendedChartForm, h])
  have hω : ω (e.symm y) ≠ 0 := by
    intro h
    apply hne
    have hz : pullbackForm e.symm ω y = 0 := by
      ext v
      simp [pullbackForm, h]
    simp [extendedChartForm, hyt, hz]
  exact ⟨e.symm y, subset_tsupport ω hω, e.right_inv hyt⟩

 theorem hasCompactSupport_extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ e.source) :
    HasCompactSupport (extendedChartForm e ω) :=
  (hc.image_of_continuousOn (e.continuousOn.mono hs)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_extendedChartForm e ω hc hs)

 theorem extendedChartForm_eventuallyEq {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) {y : Fin d → ℝ}
    (hy : y ∈ e.target) (hi : ContDiffAt ℝ 2 e.symm y)
    (hdet : (fderiv ℝ e.symm y).det ≠ 0) :
    extendedChartForm e ω =ᶠ[𝓝 y]
      (fun z => jacobianOrientation (fderiv ℝ e.symm y).det • pullbackForm e.symm ω z) := by
  have hor := jacobianOrientation_eventuallyEq
    (ContinuousLinearMap.continuous_det.continuousAt.comp (hi.continuousAt_fderiv (by simp))) hdet
  dsimp only [Function.comp_def] at hor
  filter_upwards [e.open_target.mem_nhds hy, hor] with z hz horz
  simp only [extendedChartForm, indicator_of_mem hz, horz]

/-- Compact support inside the chart makes extension by zero C1. This proves
the pullback regularity rather than adding it as a Stokes hypothesis. -/
theorem contDiff_extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ)
    (he : ContDiffOn ℝ 2 e e.source) (hi : ContDiffOn ℝ 2 e.symm e.target)
    (hω : ContDiff ℝ 1 ω) (hc : HasCompactSupport ω) (hs : tsupport ω ⊆ e.source) :
    ContDiff ℝ 1 (extendedChartForm e ω) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ e.target
  · have hiy := hi.contDiffAt (e.open_target.mem_nhds hy)
    have hdet := chart_inverse_det_ne_zero e
      (fun x hx => (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp))
      (fun x hx => (hi.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt (by simp)) hy
    have hlocal : ContDiffAt ℝ 1 (fun z => jacobianOrientation (fderiv ℝ e.symm y).det •
        pullbackForm e.symm ω z) y :=
      (contDiffAt_const (c := jacobianOrientation (fderiv ℝ e.symm y).det)).smul
        (contDiffAt_pullbackForm hiy hω.contDiffAt)
    exact hlocal.congr_of_eventuallyEq (extendedChartForm_eventuallyEq e ω hy hiy hdet)
  · have hnot : y ∉ tsupport (extendedChartForm e ω) := by
      intro h
      obtain ⟨x, hx, rfl⟩ := tsupport_extendedChartForm e ω hc hs h
      exact hy (e.map_source (hs hx))
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hnot)

/-- On the target, the derivative of the oriented extension is the oriented
pullback of the derivative. The orientation is locally constant. -/
theorem extDeriv_extendedChartForm {d n : ℕ}
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (ω : (Fin d → ℝ) → (Fin d → ℝ) [⋀^Fin n]→L[ℝ] ℝ) {y : Fin d → ℝ}
    (hy : y ∈ e.target) (hi : ContDiffAt ℝ 2 e.symm y)
    (hdet : (fderiv ℝ e.symm y).det ≠ 0) (hω : DifferentiableAt ℝ ω (e.symm y)) :
    extDeriv (extendedChartForm e ω) y =
      jacobianOrientation (fderiv ℝ e.symm y).det •
        (extDeriv ω (e.symm y)).compContinuousLinearMap (fderiv ℝ e.symm y) := by
  rw [(extendedChartForm_eventuallyEq e ω hy hi hdet).extDeriv_eq]
  change extDeriv (jacobianOrientation (fderiv ℝ e.symm y).det • pullbackForm e.symm ω) y = _
  rw [extDeriv_smul]
  unfold pullbackForm
  rw [extDeriv_pullback hω hi (by simp)]

end MahlerStokes

end

end OAI
