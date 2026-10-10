import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSampleDerivativeBound
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffSymbolSampling
import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianDirectionalCalculus
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace OAI

/-! # The derivative of the cutoff contributes only an inverse-radius error -/

open Set Filter Topology
open scoped SchwartzMap LineDeriv ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem schwartzCutoff_lineDeriv_compact (χ : 𝓢(E, ℂ))
    (hχ : HasCompactSupport (χ : E → ℂ)) (v : E) :
    HasCompactSupport ((∂_{v} χ : 𝓢(E, ℂ)) : E → ℂ) :=
  HasCompactSupport.fderiv_apply ℝ hχ v

theorem schwartzCutoff_lineDeriv_zero (χ : 𝓢(E, ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0) (v : E) :
    ∀ y : E, 1 ≤ ‖y‖ → (∂_{v} χ) y = 0 := by
  have he : EqOn (fun y => (∂_{v} χ) y) (fun _ => 0) (Metric.closedBall (0 : E) 1)ᶜ := by
    intro y hy
    have hn : 1 < ‖y‖ := by simpa only [mem_compl_iff, Metric.mem_closedBall,
      dist_zero_right, not_le] using hy
    have hloc : (χ : E → ℂ) =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [((isOpen_lt continuous_const continuous_norm).mem_nhds hn)] with z hz
      exact hχzero z hz.le
    change fderiv ℝ (χ : E → ℂ) y v = 0
    rw [hloc.fderiv_eq]
    simp
  have hc := he.closure (∂_{v} χ).continuous continuous_const
  rw [closure_compl, interior_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hc
  intro y hy
  exact hc (by simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hy)

theorem cutoffProfileSchwartz_lineDeriv (L : ℝ) (hL : 0 < L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (v : E) :
    ∂_{v} (cutoffProfileSchwartz L hL χ hχ Q hQ) =
      cutoffProfileSchwartz L hL χ hχ (cartesianDerivative v Q)
        (cartesianDerivative_contDiff Q hQ v) +
      L⁻¹ • cutoffProfileSchwartz L hL (∂_{v} χ)
        (schwartzCutoff_lineDeriv_compact χ hχ v) Q hQ := by
  ext y
  change fderiv ℝ (fun z => χ (L⁻¹ • z) * Q z) y v = _
  have hc : DifferentiableAt ℝ (fun z : E => χ (L⁻¹ • z)) y :=
    χ.differentiableAt.comp y (differentiableAt_id.const_smul L⁻¹)
  rw [fderiv_fun_mul hc (hQ.differentiable (by simp) y)]
  simp only [add_apply, smul_apply, smul_eq_mul,
    cutoffProfileSchwartz_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, cartesianDerivative]
  rw [fderiv_comp_smul]
  simp only [smul_apply, Complex.real_smul]
  ring

end DefocusingNLS

end OAI
