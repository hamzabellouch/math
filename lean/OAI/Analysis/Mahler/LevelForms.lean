import OAI.Analysis.Mahler.ExteriorHessian
import OAI.Analysis.Mahler.NormSquareForm

namespace OAI

open Complex
open scoped Topology

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {ι : Type*} [Fintype ι]

lemma contDiffAt_energy_of_open {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    ContDiffAt ℝ 2 (energy f) x := by
  have hc (j : ι) : ContDiffAt ℝ 2 (f j) x :=
    ((contDiffOn_nat_of_differentiableOn_open hU 2 (hf j)).contDiffAt
      (hU.mem_nhds hx)).restrict_scalars ℝ
  apply ContDiffAt.sum
  intro j hj
  exact (Complex.conjCLE.contDiff.contDiffAt.comp x (hc j)).mul (hc j)

omit [FiniteDimensional ℂ E] in
lemma dc_logTau_eq_div [FiniteDimensional ℂ E] {f : ι → E → ℂ} {x v : E}
    (hf : ∀ j, DifferentiableAt ℂ (f j) x) (ht : 0 < tau f x) :
    dc (logTau f) x v = dc (energy f) x v / energy f x := by
  have hp : energy f x ∈ slitPlane := by
    rw [energy_eq_tau]; exact Complex.ofReal_mem_slitPlane.mpr ht
  have hh := ((Complex.hasDerivAt_log hp).hasFDerivAt.restrictScalars ℝ).comp x
    (differentiable_energy hf).hasFDerivAt
  change HasFDerivAt (fun y => Complex.log (energy f y)) _ x at hh
  rw [logTau_eq, dc, hh.fderiv]
  simp [dc]
  ring

/-- On tangent vectors to an energy level, the actual exterior log form is
energy^{-1} times the energy form. This is local calculus, not Stokes. -/
theorem extDeriv_logTau_on_level {f : ι → E → ℂ} {U : Set E} {x : E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (ht : 0 < tau f x) (v w : E)
    (hv : fderiv ℝ (energy f) x v = 0) (hw : fderiv ℝ (energy f) x w = 0) :
    extDeriv (oneForm (dcLinear (logTau f))) x ![v, w] =
      (energy f x)⁻¹ * extDeriv (oneForm (dcLinear (energy f))) x ![v, w] := by
  have he := contDiffAt_energy_of_open hU hx hf
  have hde := differentiableAt_dcLinear he
  have hdl := differentiableAt_dcLinear (contDiffAt_logTau_of_open hU hx hf ht)
  have hfe := differentiable_energy (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx))
  have hn : energy f x ≠ 0 := by rw [energy_eq_tau]; exact_mod_cast ne_of_gt ht
  have hc : ContinuousAt (tau f) x := tau_continuousAt
    (fun j => (hf j x hx).differentiableAt (hU.mem_nhds hx))
  have hval (a b : E) (hb : fderiv ℝ (energy f) x b = 0) :
      fderiv ℝ (fun y => dcLinear (logTau f) y a) x b =
        (energy f x)⁻¹ * fderiv ℝ (fun y => dcLinear (energy f) y a) x b := by
    have heq : (fun y => dcLinear (logTau f) y a) =ᶠ[𝓝 x]
        (fun y => (energy f y)⁻¹ * dcLinear (energy f) y a) := by
      filter_upwards [hU.mem_nhds hx, hc.eventually (lt_mem_nhds ht)] with y hy hty
      simp only [dcLinear_apply, dc_logTau_eq_div
        (fun j => (hf j y hy).differentiableAt (hU.mem_nhds hy)) hty, div_eq_mul_inv]
      ring
    rw [heq.fderiv_eq]
    have hi := ((hasDerivAt_inv hn).hasFDerivAt.restrictScalars ℝ).comp x hfe.hasFDerivAt
    have ha := hde.hasFDerivAt.clm_apply (hasFDerivAt_const a x)
    have hh := hi.mul ha
    change HasFDerivAt (fun y => (energy f y)⁻¹ * dcLinear (energy f) y a) _ x at hh
    rw [hh.fderiv]
    have hae := congrArg (fun L : E →L[ℝ] ℂ => L b) ha.fderiv
    simp at hae
    simp [hb, hae]
  rw [extDeriv_oneForm hdl, extDeriv_oneForm hde, hval w v hv, hval v w hw]
  ring

end Mahler

end OAI
