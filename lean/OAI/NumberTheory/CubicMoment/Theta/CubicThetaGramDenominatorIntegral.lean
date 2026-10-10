import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKloosterman
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramKernelIntegralScaling

namespace OAI

/-! A single literal denominator contribution to the positive Gram integral.
This interface keeps its arithmetic coefficient separate from its exact
archimedean integral. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

def cubicThetaGramDenominatorIntegral (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    (c : Eisenstein) (ε : ℝ) : ℂ :=
  ∫ v in Ioi ε,star (W v)/(v:ℂ)^3*cubicThetaGramKloostermanTerm h k V c v

lemma cubicThetaGramDenominatorIntegral_eq (h k : Eisenstein) (W V : C_c(ℝ,ℂ))
    {c : Eisenstein} (hc : (3:Eisenstein)∣c) (hc0 : c≠0) (ε : ℝ) :
    cubicThetaGramDenominatorIntegral h k W V c ε=
      cubicThetaKloostermanSum h k c hc*cubicThetaArchimedeanGram h k W V (c:ℂ) ε := by
  unfold cubicThetaGramDenominatorIntegral cubicThetaArchimedeanGram
  simp only [cubicThetaGramKloostermanTerm,dite_eq_left (And.intro hc hc0)]
  simp_rw [show ∀ v : ℝ,star (W v)/(v:ℂ)^3*
      (cubicThetaKloostermanSum h k c hc*∫ z,cubicThetaGramInversionKernel h k V (c:ℂ) z v)=
        cubicThetaKloostermanSum h k c hc*
          (star (W v)/(v:ℂ)^3*∫ z,cubicThetaGramInversionKernel h k V (c:ℂ) z v) by
    intro v; ring]
  exact integral_const_mul _ _

end CubicFirstMoment

end

end OAI
