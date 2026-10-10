import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramDenominator
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanIntegral

namespace OAI

/-! The exact horizontal Fourier coefficient of a positive-cutoff Poincare
profile: the identity row and finitely many canonical Kloosterman sums. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaGramKloostermanTerm (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (c : Eisenstein) (v : ℝ) : ℂ :=
  if hc : (3:Eisenstein)∣c ∧ c≠0 then cubicThetaKloostermanSum h k c hc.1*
    ∫ z,cubicThetaGramInversionKernel h k V (c:ℂ) z v else 0

lemma cubicThetaGramDenominatorBlock_integrable (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) (c : Eisenstein) :
    IntegrableOn (fun z => cubicThetaGramDenominatorBlock h k V c (z,v))
      cubicThetaHorizontalCell := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · simp only [cubicThetaGramDenominatorBlock,dite_eq_left hc]
    exact cubicThetaKloostermanRow_integrable h k hc.1 hc.2 V hsm hδ hv hV
  · simp only [cubicThetaGramDenominatorBlock,dite_eq_right hc]
    exact integrable_zero _ _ _

lemma cubicThetaGramDenominatorBlock_integral (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ)) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) (c : Eisenstein) :
    (∫ z in cubicThetaHorizontalCell,cubicThetaGramDenominatorBlock h k V c (z,v))=
      cubicThetaGramKloostermanTerm h k V c v := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · simp only [cubicThetaGramDenominatorBlock,cubicThetaGramKloostermanTerm,dite_eq_left hc]
    exact cubicThetaKloostermanRow_integral h k hc.1 hc.2 V hsm hδ hv hV
  · simp only [cubicThetaGramDenominatorBlock,cubicThetaGramKloostermanTerm,
      dite_eq_right hc,integral_zero]

theorem cubicThetaPositiveProfile_fourier_kloosterman (h k : Eisenstein)
    (V : C_c(ℝ,ℂ)) (hsm : ContDiff ℝ ∞ (V : ℝ → ℂ))
    {ε δ v : ℝ} (hε : 0<ε) (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) (hv : ε≤v) :
    cubicThetaHorizontalFourierCoefficient h (fun z => cubicThetaFourierProfileSeries k (z,v) V)=
      V v*cubicThetaHorizontalFourierCoefficient h (cubicThetaHorizontalCharacter k)+
      ∑ c∈cubicThetaGramDenominators ε δ,cubicThetaGramKloostermanTerm h k V c v := by
  have hv0 := hε.trans_le hv
  have hd : IntegrableOn (fun z => star (cubicThetaHorizontalCharacter h z)*
      cubicThetaFourierProfileTerm k cubicThetaZeroRow (z,v) V) cubicThetaHorizontalCell := by
    obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
    have he : (fun z => star (cubicThetaHorizontalCharacter h z)*
        cubicThetaFourierProfileTerm k cubicThetaZeroRow (z,v) V)=
        (fun z => star (cubicThetaHorizontalCharacter h z)*(V v*cubicThetaHorizontalCharacter k z)) := by
      funext z
      rw [cubicThetaFourierProfileTerm_zeroRow k V hv0]
    rw [he]
    exact (((cubicThetaHorizontalCharacter_continuous h).star.mul
      (continuous_const.mul (cubicThetaHorizontalCharacter_continuous k))).continuousOn.integrableOn_compact hK).mono_set hsub
  have hci (c : Eisenstein) := cubicThetaGramDenominatorBlock_integrable h k V hsm hδ hv0 hV c
  unfold cubicThetaHorizontalFourierCoefficient
  have he (z : ℂ) := cubicThetaGramRows_finite_denominators h k V hε hδ hV (p:=(z,v)) hv
  simp_rw [he]
  rw [integral_add hd (integrable_finsetSum _ (fun c _ => hci c)),integral_finsetSum _ (fun c _ => hci c)]
  simp_rw [cubicThetaGramDenominatorBlock_integral h k V hsm hδ hv0 hV]
  congr 1
  rw [←integral_const_mul]
  apply setIntegral_congr_fun cubicThetaHorizontalCell_measurable
  intro z _
  dsimp only
  rw [cubicThetaFourierProfileTerm_zeroRow k V hv0]
  ring

end CubicFirstMoment

end

end OAI
