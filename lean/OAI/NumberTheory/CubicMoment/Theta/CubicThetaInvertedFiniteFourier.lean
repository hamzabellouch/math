import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryConstant
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPrimaryContinuation

namespace OAI

/-! The actual finite Fourier coefficient of an inverted row is the
middle primary twist already continued from the global Eisenstein series. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaInvertedGaussCoefficient (c h : Eisenstein) : ℂ :=
  ∑' x : Residues c, cubicSymbol c (3*residueRepresentative c x)*
    (Real.fourierChar (tracePair (residueRepresentative c x:ℂ)
      ((h:ℂ)/((c:ℂ)*traceLambda))):ℂ)

lemma cubicThetaInvertedGaussCoefficient_factor {c : Eisenstein} (hc : primary c)
    (h : Eisenstein) :
    cubicThetaInvertedGaussCoefficient c h=
      cubicSymbol c 3*cubicThetaSymbolFourier c (primary_ne_zero hc) h := by
  unfold cubicThetaInvertedGaussCoefficient cubicThetaSymbolFourier
  rw [←tsum_mul_left]
  apply tsum_congr
  intro x
  rw [cubicSymbol_mul_upper hc,residueFourierChar_mk_mul]
  ring

lemma cubicThetaInvertedGaussCoefficient_zero (c : Eisenstein) :
    cubicThetaInvertedGaussCoefficient c 0=cubicThetaInvertedConstantGauss c := by
  simp [cubicThetaInvertedGaussCoefficient,cubicThetaInvertedConstantGauss,tracePair]

lemma cubicThetaSymbol_three {c : Eisenstein} (hc : primary c) :
    cubicSymbol c 3=(cubicSymbol c lambdaE)^2 := by
  have he := cubicSymbol_pow_upper hc lambdaE 2
  rw [lambdaE_sq,cubicSymbol_neg hc] at he
  exact he

def cubicThetaInvertedFrequencyDirichlet (h : Eisenstein) (s : ℂ) : ℂ :=
  ∑' c : CubicThetaPrimaryPart, cubicThetaInvertedGaussCoefficient c.val h*(norm c.val:ℂ)^(-s)

lemma cubicThetaInvertedFrequencyDirichlet_eq (h : Eisenstein) (s : ℂ) :
    cubicThetaInvertedFrequencyDirichlet h s=cubicThetaPrimaryFourierSeries 1 1 s h := by
  unfold cubicThetaInvertedFrequencyDirichlet cubicThetaPrimaryFourierSeries
  apply tsum_congr
  intro c
  rw [cubicThetaInvertedGaussCoefficient_factor c.property,cubicThetaSymbol_three c.property]
  have h1 : cubicSymbol c.val 1=1 := by
    rw [cubic_reciprocity c.property primary_one,cubicSymbol_one_lower]
  simp [cubicThetaPrimaryFourierTerm,h1]

theorem cubicThetaRegularizedInvertedFrequency_right {h : Eisenstein} (hh : h≠0)
    {s : ℂ} (hs : 3<s.re) :
    cubicThetaRegularizedPrimaryOne h s=(s-4/3)*cubicThetaInvertedFrequencyDirichlet h s := by
  rw [cubicThetaInvertedFrequencyDirichlet_eq]
  exact cubicThetaRegularizedPrimaryOne_right hh hs

end CubicFirstMoment

end

end OAI
