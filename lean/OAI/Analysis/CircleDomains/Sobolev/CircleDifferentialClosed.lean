import OAI.Analysis.CircleDomains.Topology.CircleCovectors
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

namespace OAI

/-! The intrinsic differential of a smooth circle coordinate is closed.
The proof uses actual local real branches and symmetry of their Hessians. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem circleFDeriv_partial_commute
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → UnitAddCircle} {U : Set E} (hU : IsOpen U) (hf : SmoothCircleOn f U)
    {x : E} (hx : x ∈ U) (v w : E) :
    (fderiv ℝ (fun y => circleFDeriv f y w) x) v =
      (fderiv ℝ (fun y => circleFDeriv f y v) x) w := by
  let a := circleCut f x
  let V := U ∩ f ⁻¹' ({(a : UnitAddCircle)} : Set UnitAddCircle)ᶜ
  have hV : IsOpen V := hf.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hxV : x ∈ V := ⟨hx, circleCut_ne f x⟩
  have hu : ContDiffOn ℝ (⊤ : ℕ∞) (circleBranch f a) V := by
    intro y hy
    exact (hf y hy.1 a hy.2).contDiffWithinAt
  have heq := circleFDeriv_eventuallyEq_lift hV (hf.continuousOn.mono inter_subset_left)
    hu (fun y _ => coe_circleBranch f a y) hxV
  have hp (z : E) : (fun y => circleFDeriv f y z) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ (circleBranch f a) y) z) :=
    heq.mono fun _ h => congrArg (fun L : E →L[ℝ] ℝ => L z) h
  rw [(hp w).fderiv_eq, (hp v).fderiv_eq]
  have huAt := hu.contDiffAt (hV.mem_nhds hxV)
  have hdu : DifferentiableAt ℝ (fderiv ℝ (circleBranch f a)) x :=
    (huAt.fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hdu (differentiableAt_const w),
    fderiv_clm_apply hdu (differentiableAt_const v)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add]
  exact huAt.isSymmSndFDerivAt (by simp) v w

 theorem circleFDeriv_closed_complex
    {f : ℂ → UnitAddCircle} {U : Set ℂ} (hU : IsOpen U) (hf : SmoothCircleOn f U)
    {z : ℂ} (hz : z ∈ U) :
    (fderiv ℝ (fun x => circleFDeriv f x Complex.I) z) 1 =
      (fderiv ℝ (fun x => circleFDeriv f x 1) z) Complex.I :=
    circleFDeriv_partial_commute hU hf hz 1 Complex.I

end CircleDomainRigidity.FiniteTransfer

end

end OAI
