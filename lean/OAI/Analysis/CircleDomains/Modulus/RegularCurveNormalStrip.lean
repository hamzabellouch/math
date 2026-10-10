import OAI.Analysis.CircleDomains.Topology.PlanarFormPullback
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! The actual normal-strip map of a regular smooth planar curve has
positive Jacobian at its central curve. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

def curveNormalStrip (γ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  γ p.1 + p.2 • (Complex.I * deriv γ p.1)

lemma curveNormalStrip_contDiff {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (curveNormalStrip γ) := by
  have hd : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  exact (hγ.comp contDiff_fst).add
    (contDiff_snd.smul (contDiff_const.mul (hd.comp contDiff_fst)))

lemma curveNormalStrip_fderiv {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (t : ℝ) (v : ℝ × ℝ) :
    (fderiv ℝ (curveNormalStrip γ) (t,0)) v =
      v.1 • deriv γ t + v.2 • (Complex.I * deriv γ t) := by
  have hd : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  have hfst : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (t,0) :=
    hasFDerivAt_fst
  have hγd : HasFDerivAt γ
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv γ t)) t :=
    (hγ.differentiable (by simp) t).hasDerivAt
  have h1 := hγd.comp (t,(0 : ℝ)) hfst
  have hN : DifferentiableAt ℝ (fun p : ℝ × ℝ => Complex.I * deriv γ p.1) (t,0) :=
    (contDiff_const.mul (hd.comp contDiff_fst)).differentiable (by simp) (t,0)
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := (t,0))).smul hN.hasFDerivAt
  have h := h1.add h2
  change HasFDerivAt (curveNormalStrip γ) _ (t,0) at h
  rw [h.fderiv]
  simp

lemma curveNormalStrip_jacobian {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (t : ℝ) :
    ((fderiv ℝ (curveNormalStrip γ) (t,0)) (1,0)).re *
        ((fderiv ℝ (curveNormalStrip γ) (t,0)) (0,1)).im -
      ((fderiv ℝ (curveNormalStrip γ) (t,0)) (1,0)).im *
        ((fderiv ℝ (curveNormalStrip γ) (t,0)) (0,1)).re = ‖deriv γ t‖ ^ 2 := by
  simp only [curveNormalStrip_fderiv hγ,one_smul,zero_smul,add_zero,zero_add,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_sub]
  rw [Complex.sq_norm,Complex.normSq_apply]
  ring

end CircleDomainRigidity

end

end OAI
