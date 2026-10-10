import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramIntegralDecomposition

namespace OAI

/-! The exact prime-free correction in the common-cube Gram identity. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaGramCubeMultiplier_sum (p : Eisenstein) (S : Finset Eisenstein)
    (f : Eisenstein → ℂ) :
    (∑ d∈S,cubicThetaGramCubeMultiplier p d*f d)=
      (norm (p^3):ℂ)*(∑ d∈S,f d)-
        (norm (p^2):ℂ)*∑ d∈S.filter (fun d => ¬p∣d),f d := by
  rw [Finset.mul_sum,Finset.mul_sum,Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  unfold cubicThetaGramCubeMultiplier
  by_cases hd : p∣d <;> simp [hd]
  ring

theorem cubicThetaGramPrimePart_cube_correction {p : Eisenstein} (hp : primaryPrime p)
    (h k : Eisenstein) (W V : C_c(ℝ,ℂ)) {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ)
    (hV : ∀ t≤δ,V t=0) :
    cubicThetaGramPrimePart p (p^3*h) (p^3*k)
      (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
        (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) W)
      (cubicThetaRadialWeightScale ‖((p^3:Eisenstein):ℂ)‖
        (norm_pos_iff.mpr (fun he => (pow_ne_zero 3 hp.2.ne_zero) (Subtype.ext he))) V)
      (ε/‖((p^3:Eisenstein):ℂ)‖) (δ/‖((p^3:Eisenstein):ℂ)‖)=
      (norm (p^3):ℂ)*(cubicThetaKloostermanGram h k W V ε δ-
        cubicThetaGramIdentityPart h k W V ε)-
      (norm (p^2):ℂ)*cubicThetaGramPrimeFreePart p h k W V ε δ := by
  have hi := cubicThetaGram_sum_integrable h k W V hε hδ hV (cubicThetaGramDenominators ε δ)
  have hif := cubicThetaGram_sum_integrable h k W V hε hδ hV
    ((cubicThetaGramDenominators ε δ).filter (fun d => ¬p∣d))
  have hg : cubicThetaKloostermanGram h k W V ε δ-cubicThetaGramIdentityPart h k W V ε=
      ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
        ∑ d∈cubicThetaGramDenominators ε δ,cubicThetaGramKloostermanTerm h k V d v := by
    unfold cubicThetaKloostermanGram cubicThetaGramIdentityPart
    simp_rw [mul_add]
    rw [integral_add (cubicThetaGramIdentity_integrable h k W V hε) hi]
    ring
  rw [cubicThetaGramPrimePart_cube hp h k W V hε hδ,hg]
  change (∫ v in Ioi ε,star (W v)/(v:ℂ)^3*
      ∑ d∈cubicThetaGramDenominators ε δ,cubicThetaGramCubeMultiplier p d*
        cubicThetaGramKloostermanTerm h k V d v)=_
  calc
    _ = ∫ v in Ioi ε,(norm (p^3):ℂ)*(star (W v)/(v:ℂ)^3*
        ∑ d∈cubicThetaGramDenominators ε δ,cubicThetaGramKloostermanTerm h k V d v)-
      (norm (p^2):ℂ)*(star (W v)/(v:ℂ)^3*
        ∑ d∈(cubicThetaGramDenominators ε δ).filter (fun d => ¬p∣d),
          cubicThetaGramKloostermanTerm h k V d v) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp only
      rw [cubicThetaGramCubeMultiplier_sum]
      ring
    _ = _ := by rw [integral_sub (hi.const_mul _) (hif.const_mul _),
      integral_const_mul,integral_const_mul]; rfl

end CubicFirstMoment

end

end OAI
