import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedContour
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothMellin

namespace OAI

/-! Mellin inversion for the literal primary-selected coefficients
at every primary rational cusp. -/
noncomputable section
open MeasureTheory Set
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicTheta_twisted_angular_bound {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n,‖a n‖≤C) (z : ℂ) (ℓ : ℤ) (n : Eisenstein) :
    ‖theta ℓ n*cubicThetaCoefficientTwist a z n‖≤C := by
  by_cases hn : n=0
  · subst n
    by_cases hℓ : ℓ=0
    · simpa only [hℓ,theta_zero,one_mul,cubicThetaCoefficientTwist_norm] using ha 0
    · simpa [theta,zero_zpow ℓ hℓ] using hC
  · rw [norm_mul,norm_theta hn,one_mul,cubicThetaCoefficientTwist_norm]
    exact ha n

def cubicThetaSelectedAdditiveSum (g : SL(2,Eisenstein)) (rev : Bool) (k : ℕ)
    (W : ℝ→ℂ) (Z : ℝ) : ℂ :=
  ∑' n : MetaplecticDualArgument,theta (cubicThetaCircleOrder (!rev) k) n.val*
    cubicThetaCoefficientTwist cubicThetaSelectedCoefficient (cubicThetaPrimaryCuspCenter g) n.val*
      (‖cubicThetaFrequency n.val‖:ℂ)*W (‖cubicThetaFrequency n.val‖^2/Z)

theorem cubicThetaSelected_smooth_continued (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ Z : ℝ} (hσ : 3/2<σ) (hZ : 0<Z) :
    cubicThetaSelectedAdditiveSum g rev k W Z=
      ((1/(2*Real.pi):ℝ):ℂ)*∫ t : ℝ,
        mellin W (σ+(t:ℂ)*Complex.I)*(Z:ℂ)^(σ+(t:ℂ)*Complex.I)*
          cubicThetaSelectedDirichlet g hc rev k (σ+(t:ℂ)*Complex.I) := by
  have ha (n : Eisenstein) : ‖theta (cubicThetaCircleOrder (!rev) k) n*
      cubicThetaCoefficientTwist cubicThetaSelectedCoefficient (cubicThetaPrimaryCuspCenter g) n‖≤81 :=
    cubicTheta_twisted_angular_bound (by norm_num) cubicThetaSelectedCoefficient_norm _ _ n
  unfold cubicThetaSelectedAdditiveSum
  rw [cubicTheta_smooth_mellin (by norm_num) ha W hW hpos hsm hσ hZ]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [cubicThetaSelectedDirichlet_initial g hc rev hk (by simpa using hσ)]

end CubicFirstMoment

end

end OAI
