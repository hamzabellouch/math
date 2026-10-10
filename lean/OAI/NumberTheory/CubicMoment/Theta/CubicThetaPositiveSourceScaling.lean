import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierScaling

namespace OAI

/-! Exact composition of radial scalings and proof-independent positive
Fourier sources. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaRadialWeightScale_one (W : C_c(ℝ,ℂ)) :
    cubicThetaRadialWeightScale 1 zero_lt_one W=W := by
  ext v
  change W (1*v)=W v
  rw [one_mul]

lemma cubicThetaRadialWeightScale_comp (r s : ℝ) (hr : 0<r) (hs : 0<s)
    (W : C_c(ℝ,ℂ)) :
    cubicThetaRadialWeightScale s hs (cubicThetaRadialWeightScale r hr W)=
      cubicThetaRadialWeightScale (r*s) (mul_pos hr hs) W := by
  ext v
  change W (r*(s*v))=W ((r*s)*v)
  rw [mul_assoc]

lemma cubicThetaPositiveFourierMass_congr {h k : Eisenstein} {W V : C_c(ℝ,ℂ)}
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hW : ∀ v≤ε,W v=0) (hV : ∀ v≤δ,V v=0)
    (hsmW : ContDiff ℝ ∞ (W : ℝ → ℂ)) (hsmV : ContDiff ℝ ∞ (V : ℝ → ℂ))
    (hh : h=k) (hWV : W=V) :
    cubicThetaPositiveFourierMass h W hε hW hsmW=
      cubicThetaPositiveFourierMass k V hδ hV hsmV := by
  subst k V
  rfl

end CubicFirstMoment

end

end OAI
