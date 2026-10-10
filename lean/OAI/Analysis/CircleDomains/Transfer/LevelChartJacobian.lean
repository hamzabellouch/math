import OAI.Analysis.CircleDomains.Transfer.ComplexC1LevelChart
import OAI.Analysis.CircleDomains.Sobolev.ComplexCoareaJacobian

namespace OAI

/-! The inverse level chart has the exact Jacobian factor needed by coarea. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma level_chart_inverse_jacobian
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (e : OpenPartialHomeomorph ℂ ℂ) (heD : e.source ⊆ D)
    (he : ∀ z, (e z).re = f z) (heI : ContDiffOn ℝ 1 e.symm e.target)
    {y : ℂ} (hy : y ∈ e.target) :
    ‖fderiv ℝ f (e.symm y)‖ * |(fderiv ℝ e.symm y).det| =
      ‖fderiv ℝ e.symm y Complex.I‖ := by
  have hA := (hf.contDiffAt (hD.mem_nhds (heD (e.map_target hy)))).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hB := (heI.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hfun : (f ∘ e.symm) =ᶠ[𝓝 y] Complex.re := by
    filter_upwards [e.open_target.mem_nhds hy] with w hw
    change f (e.symm w) = w.re
    rw [← he, e.right_inv hw]
  have hder : (fderiv ℝ f (e.symm y)).comp (fderiv ℝ e.symm y) = Complex.reCLM :=
    ((hA.hasFDerivAt.comp y hB.hasFDerivAt).congr_of_eventuallyEq hfun.symm).unique
      Complex.reCLM.hasFDerivAt
  apply coarea_covector_jacobian
  · have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) hder
    simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.one_re] using h
  · have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hder
    simpa only [ContinuousLinearMap.comp_apply, Complex.reCLM_apply, Complex.I_re] using h

end CircleDomainRigidity

end

end OAI
