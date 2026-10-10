import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveInteriorSource
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveSourceScaling
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveSquareSource

namespace OAI

/-! The literal positive-cutoff source orbit under prime-cube dilation. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

def cubicThetaPrimeFourierOrbit {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (k : ℕ) :
    cubicThetaAutomorphicL2 :=
  cubicThetaPositiveFourierMass (p^(3*k)*h)
    (cubicThetaRadialWeightScale ((‖(p:ℂ)‖^3)^k)
      (pow_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) k) W)
    (div_pos hε (pow_pos (pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3) k))
    (cubicThetaRadialWeightScale_positive_low _ W hW)
    (cubicThetaRadialWeightScale_smooth _ _ W hsm)

lemma cubicThetaPrimeFourierOrbit_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaPrimeFourierOrbit hp h W hε hW hsm 0=
      cubicThetaPositiveFourierMass h W hε hW hsm := by
  unfold cubicThetaPrimeFourierOrbit
  simp only [Nat.mul_zero,pow_zero,one_mul]
  exact cubicThetaPositiveFourierMass_congr _ _ _ _ _ _ rfl (cubicThetaRadialWeightScale_one W)

theorem cubicThetaPrimeFourierOrbit_step {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (k : ℕ) :
    cubicThetaPrimeCubeHeckeMass hp (cubicThetaPrimeFourierOrbit hp h W hε hW hsm (k+1))=
      (((‖(p:ℂ)‖^3)^2:ℝ):ℂ) • cubicThetaPrimeFourierOrbit hp h W hε hW hsm k+
        cubicThetaPrimeFourierOrbit hp h W hε hW hsm (k+2) := by
  let r := ‖(p:ℂ)‖^3
  have hr : 0<r := pow_pos (norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))) 3
  let V := cubicThetaRadialWeightScale (r^(k+1)) (pow_pos hr _) W
  have hV : ∀ v≤ε/r^(k+1),V v=0 := cubicThetaRadialWeightScale_positive_low _ W hW
  have hVs : ContDiff ℝ ∞ (V : ℝ → ℂ) := cubicThetaRadialWeightScale_smooth _ _ W hsm
  have he := cubicThetaPositiveInteriorSource hp (p^(3*k)*h) V (div_pos hε (pow_pos hr _)) hV hVs
  have heq : p^3*(p^(3*k)*h)=p^(3*(k+1))*h := by
    rw [show 3*(k+1)=3+3*k by omega,pow_add]
    ring
  have heq2 : p^3*(p^3*(p^(3*k)*h))=p^(3*(k+2))*h := by
    rw [show 3*(k+2)=3+3+3*k by omega,pow_add,pow_add]
    ring
  have hi : cubicThetaRadialWeightScale r⁻¹ (inv_pos.mpr hr) V=
      cubicThetaRadialWeightScale (r^k) (pow_pos hr _) W := by
    rw [cubicThetaRadialWeightScale_comp]
    have hpow : r^(k+1)*r⁻¹=r^k := by rw [pow_succ,mul_assoc,mul_inv_cancel₀ hr.ne',mul_one]
    congr 1
  have ho : cubicThetaRadialWeightScale r hr V=
      cubicThetaRadialWeightScale (r^(k+2)) (pow_pos hr _) W := by
    rw [cubicThetaRadialWeightScale_comp]
    congr 1
  have hleft : cubicThetaPositiveFourierMass (p^3*(p^(3*k)*h)) V
      (div_pos hε (pow_pos hr _)) hV hVs=
      cubicThetaPrimeFourierOrbit hp h W hε hW hsm (k+1) := by
    unfold cubicThetaPrimeFourierOrbit
    exact cubicThetaPositiveFourierMass_congr _ _ _ _ _ _ heq rfl
  rw [hleft] at he
  convert he using 1
  congr 1
  · congr 1
    unfold cubicThetaPrimeFourierOrbit
    exact (cubicThetaPositiveFourierMass_congr _ _ _ _ _ _ rfl hi).symm
  · unfold cubicThetaPrimeFourierOrbit
    exact (cubicThetaPositiveFourierMass_congr _ _ _ _ _ _ heq2 ho).symm

lemma cubicThetaPrimeFourierOrbit_square_start {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) (W : C_c(ℝ,ℂ)) {ε : ℝ} (hε : 0<ε)
    (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaPrimeCubeHeckeMass hp (cubicThetaPrimeFourierOrbit hp (p^2*h) W hε hW hsm 0)=
      cubicThetaPrimeFourierOrbit hp (p^2*h) W hε hW hsm 1 := by
  rw [cubicThetaPrimeFourierOrbit_zero,cubicThetaPositiveSquareSource hp h hh W hε hW hsm]
  unfold cubicThetaPrimeFourierOrbit
  simp only [Nat.mul_one,pow_one]

end CubicFirstMoment

end

end OAI
