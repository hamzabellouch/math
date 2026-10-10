import OAI.Analysis.CircleDomains.Reflection.AnalyticJordanParametrization
import OAI.Analysis.CircleDomains.Sobolev.HolomorphicInjOnDerivative
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Basic

namespace OAI

/-! The actual smooth plane chart and inverse supplied by a holomorphic
injection on an open set. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 def holomorphicPlaneChart {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    OpenPartialHomeomorph ℂ ℂ where
  toPartialEquiv := hi.toPartialEquiv f U
  open_source := hU
  open_target := holomorphic_injOn_isOpen_image hU hf hi hU Subset.rfl
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := by
    rintro y ⟨x,hx,rfl⟩
    exact (continuousAt_holomorphic_invFunOn hU hf hi hx).continuousWithinAt

lemma holomorphicPlaneChart_smooth {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    ContDiffOn ℝ ∞ (holomorphicPlaneChart hU hf hi) U := by
  intro x hx
  exact ((hf.analyticAt (hU.mem_nhds hx)).contDiffAt.restrict_scalars ℝ).contDiffWithinAt

lemma holomorphicPlaneChart_inverse_smooth {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) :
    ContDiffOn ℝ ∞ (holomorphicPlaneChart hU hf hi).symm (f '' U) := by
  intro y hy
  let e := holomorphicPlaneChart hU hf hi
  have hx : e.symm y∈U := e.map_target hy
  have hd : HasDerivAt (e : ℂ → ℂ) (deriv f (e.symm y)) (e.symm y) :=
    ((hf _ hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hs : ContDiffAt ℂ ∞ (e : ℂ → ℂ) (e.symm y) :=
    (hf.analyticAt (hU.mem_nhds hx)).contDiffAt
  exact ((e.contDiffAt_symm_deriv (holomorphicInjOn_deriv_ne_zero hU hf hi hx)
    hy hd hs).restrict_scalars ℝ).contDiffWithinAt

end CircleDomainRigidity

end

end OAI
