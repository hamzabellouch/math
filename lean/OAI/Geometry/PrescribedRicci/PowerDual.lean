import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev

namespace OAI

/-! Power Dual. -/

noncomputable section
open Filter Topology Asymptotics
namespace TameInterpolation

def powerDual (p x : ℝ) : ℝ := x * |x| ^ (p-2)

lemma powerDual_zero (p : ℝ) : powerDual p 0 = 0 := by simp [powerDual]

lemma powerDual_hasDerivAt {p : ℝ} (hp : 2 < p) (x : ℝ) :
    HasDerivAt (powerDual p) ((p-1)*|x|^(p-2)) x := by
  by_cases hx : x = 0
  · subst x
    have hq : 0 < p-2 := by linarith
    have hF : HasFDerivAt (powerDual p) (0 : ℝ →L[ℝ] ℝ) 0 := by
      refine .of_isLittleO ?_
      simp only [powerDual,abs_zero,zero_mul,zero_apply,sub_zero]
      have hsmall : (fun y : ℝ => |y|^(p-2)) =o[𝓝 0] (fun _ => (1:ℝ)) := by
        apply (isLittleO_const_iff one_ne_zero).mpr
        have hc : ContinuousAt (fun y : ℝ => |y|^(p-2)) 0 :=
          continuousAt_id.abs.rpow_const (Or.inr hq.le)
        simpa only [abs_zero,Real.zero_rpow hq.ne'] using hc.tendsto
      simpa only [mul_one,sub_zero] using (isBigO_refl (fun y : ℝ => y) (𝓝 0)).mul_isLittleO hsmall
    simpa [hq.ne'] using hF.hasDerivAt
  · have hd := (hasDerivAt_id x).mul ((hasDerivAt_abs hx).rpow_const (p:=p-2) (Or.inl (abs_ne_zero.mpr hx)))
    have ha : 0 < |x| := abs_pos.mpr hx
    have he : |x|^(p-2) = |x|^(p-2-1)*|x| := by
      rw [← Real.rpow_add_one ha.ne']
      congr 1
      ring
    have hs : x*(SignType.sign x : ℝ) = |x| := by
      simpa only [mul_comm] using sign_mul_self x
    have hval : (p-1)*|x|^(p-2) = 1*|x|^(p-2)+x*((SignType.sign x:ℝ)*(p-2)*|x|^(p-2-1)) := by
      rw [he]
      calc
        _ = |x|^(p-2-1)*|x|+ (x*(SignType.sign x:ℝ))*(p-2)*|x|^(p-2-1) := by rw [hs]; ring
        _ = _ := by ring
    rw [hval]
    exact hd

lemma powerDual_continuous {p : ℝ} (hp : 2 < p) : Continuous (powerDual p) :=
  (show Differentiable ℝ (powerDual p) from fun x => (powerDual_hasDerivAt hp x).differentiableAt).continuous

lemma powerDual_mul_self {p : ℝ} (hp : 2 < p) (x : ℝ) :
    powerDual p x*x = |x|^p := by
  by_cases hx : x = 0
  · simp [hx,powerDual,Real.zero_rpow (by linarith : p ≠ 0)]
  · change x * |x|^(p-2) * x = |x|^p
    conv_rhs => rw [show p = (p-2)+2 by ring,Real.rpow_add (abs_pos.mpr hx),Real.rpow_two,sq_abs]
    ring
end TameInterpolation

end

end OAI
