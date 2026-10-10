import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionMeanPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroWindow

namespace OAI

/-! Compact radial test functions under positive dilations. These are the
literal tests induced by the Hecke constant-mode identity. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaRadialWeightScale (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ)) : C_c(ℝ,ℂ) :=
  W.comp (Homeomorph.mulLeft₀ r hr.ne').toCocompactMap

lemma cubicThetaRadialWeightScale_apply (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ)) (v : ℝ) :
    cubicThetaRadialWeightScale r hr W v=W (r*v) := rfl

lemma cubicThetaRadialWeightScale_mellin (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ)) (s : ℂ) :
    mellin (star (cubicThetaRadialWeightScale r hr W)) s=
      (r:ℂ)^(-s)*mellin (star W) s := by
  have he : (star (cubicThetaRadialWeightScale r hr W) : ℝ → ℂ)=
      fun v => (star W : ℝ → ℂ) (r*v) := rfl
  rw [he,mellin_comp_mul_left _ _ hr]
  rfl

lemma cubicThetaRadialWeightScale_low (r : ℝ) (hr : 0<r) (W : C_c(ℝ,ℂ))
    (H : ℝ) (hW : ∀ v≤H,W v=0) {v : ℝ} (hv : v≤H/r) :
    cubicThetaRadialWeightScale r hr W v=0 := by
  rw [cubicThetaRadialWeightScale_apply]
  exact hW (r*v) (by nlinarith [(le_div_iff₀ hr).mp hv])

end CubicFirstMoment

end

end OAI
