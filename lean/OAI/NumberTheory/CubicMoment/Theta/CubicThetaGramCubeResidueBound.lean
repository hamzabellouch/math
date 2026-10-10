import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeRecurrence
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramResidueBound

namespace OAI

/-! The actual cubic-frequency residue is controlled by the exact
prime-free Gram correction. No bound for that correction is assumed. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

lemma cubicThetaPrimeCube_pole_scale {p : Eisenstein} (hp : primaryPrime p) :
    (‖((p^3:Eisenstein):ℂ)‖:ℂ)^(4/3:ℂ)=(norm p:ℂ)^2 := by
  have hu : 0<‖(p:ℂ)‖ := norm_pos_iff.mpr (fun he => hp.2.ne_zero (Subtype.ext he))
  have hn : ‖((p^3:Eisenstein):ℂ)‖=‖(p:ℂ)‖^3 := by
    change ‖(p:ℂ)^3‖=‖(p:ℂ)‖^3
    exact norm_pow _ _
  have he : (‖(p:ℂ)‖^3)^(4/3:ℝ)=(norm p)^2 := by
    rw [←Real.rpow_natCast ‖(p:ℂ)‖ 3,←Real.rpow_mul hu.le]
    norm_num
    rw [show norm p=‖(p:ℂ)‖^2 from Complex.normSq_eq_norm_sq _]
    ring
  rw [hn,show (4/3:ℂ)=((4/3:ℝ):ℂ) by norm_num,
    ←Complex.ofReal_cpow (pow_nonneg hu.le 3),he,Complex.ofReal_pow]

theorem cubicThetaFourierResidue_cube_gram_bound {p h : Eisenstein} (hp : primaryPrime p)
    (hh : h≠0) (W : C_c(ℝ,ℂ)) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) :
    let r := ‖((p^3:Eisenstein):ℂ)‖
    let hr : 0<r := norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))
    let V := cubicThetaRadialWeightScale r hr W
    (norm p)^4*‖((Real.pi:ℂ)/Complex.Gamma (4/3))*
      cubicThetaArithmeticFourierResidue (p^3*h) (4/3)*
        cubicThetaPositiveRadialTest h W ε (4/3)‖^2≤
      ((norm (p^3):ℂ)*cubicThetaKloostermanGram h h W W ε ε+
        cubicThetaGramPrimeFreePart p (p^3*h) (p^3*h) V V (ε/r) (ε/r)-
        (norm (p^2):ℂ)*cubicThetaGramPrimeFreePart p h h W W ε ε).re*
          ‖cubicThetaArithmeticResidueL2‖^2 := by
  dsimp only
  let r := ‖((p^3:Eisenstein):ℂ)‖
  have hr : 0<r := norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))
  let V := cubicThetaRadialWeightScale r hr W
  have hV : ∀ t≤ε/r,V t=0 := cubicThetaRadialWeightScale_positive_low hr W hW
  have hVs : ContDiff ℝ ∞ (V : ℝ → ℂ) := cubicThetaRadialWeightScale_smooth r hr W hsm
  have hi := cubicThetaFourierResidue_gram_bound (mul_ne_zero (pow_ne_zero 3 hp.2.ne_zero) hh)
    V hVs (div_pos hε hr) hV
  rw [cubicThetaPositivePoleRadialTest_scale (pow_ne_zero 3 hp.2.ne_zero) hh W hε hW,
    cubicThetaPrimeCube_pole_scale hp,
    cubicThetaKloostermanGram_cube_recurrence hp h h W W hε hε hW] at hi
  convert hi using 1
  have he (z t : ℂ) : ((Real.pi:ℂ)/Complex.Gamma (4/3))*z*((norm p:ℂ)^2*t)=
      (norm p:ℂ)^2*(((Real.pi:ℂ)/Complex.Gamma (4/3))*z*t) := by ring
  rw [he]
  conv_rhs => rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg p),mul_pow]
  ring

end CubicFirstMoment

end

end OAI
