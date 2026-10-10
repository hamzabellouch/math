import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubePrimeCorrection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramIdentityScaling

namespace OAI

/-! The exact common-cube recurrence for the full positive Gram kernel.
The remaining prime-free term is explicit, not discarded or assumed zero. -/
noncomputable section
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment

theorem cubicThetaKloostermanGram_cube_recurrence {p : Eisenstein} (hp : primaryPrime p)
    (h k : Eisenstein) (W V : C_c(ℝ,ℂ)) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hV : ∀ t≤δ,V t=0) :
    cubicThetaKloostermanGram (p^3*h) (p^3*k)
      (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
        (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) W)
      (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
        (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) V)
      (ε/‖((p^3:Eisenstein):ℂ)‖) (δ/‖((p^3:Eisenstein):ℂ)‖)=
      (norm (p^3):ℂ)*cubicThetaKloostermanGram h k W V ε δ+
      cubicThetaGramPrimeFreePart p (p^3*h) (p^3*k)
        (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
          (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) W)
        (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
          (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) V)
        (ε/‖((p^3:Eisenstein):ℂ)‖) (δ/‖((p^3:Eisenstein):ℂ)‖)-
      (norm (p^2):ℂ)*cubicThetaGramPrimeFreePart p h k W V ε δ := by
  let r := ‖((p^3:Eisenstein):ℂ)‖
  have hr : 0<r := norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))
  have hVr : ∀ t≤δ/r,cubicThetaRadialWeightScale r hr V t=0 :=
    cubicThetaRadialWeightScale_positive_low hr V hV
  rw [cubicThetaKloostermanGram_prime_split p (p^3*h) (p^3*k)
    (cubicThetaRadialWeightScale r hr W) (cubicThetaRadialWeightScale r hr V)
    (div_pos hε hr) (div_pos hδ hr) hVr,
    cubicThetaGramIdentityPart_scale _ _ _ (pow_ne_zero 3 hp.2.ne_zero),
    cubicThetaGramPrimePart_cube_correction hp h k W V hε hδ hV]
  ring

end CubicFirstMoment

end

end OAI
