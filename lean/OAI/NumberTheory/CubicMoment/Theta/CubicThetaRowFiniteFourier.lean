import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWeightFactor
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveResidueFourier

namespace OAI

/-! Finite Fourier forms of the literal row and cubic-symbol sums.
These expose the same perfect codifferent pairing for Chinese remainders. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSymbolFourier (c : Eisenstein) (hc : c≠0) (h : Eisenstein) : ℂ :=
  ∑' x : Residues c, cubicSymbol c (residueRepresentative c x)*
    residueFourierChar c hc (Ideal.Quotient.mk (modulus c) h*x)

lemma residueFourierChar_mk_mul (c : Eisenstein) (hc : c≠0) (h : Eisenstein)
    (x : Residues c) :
    residueFourierChar c hc (Ideal.Quotient.mk (modulus c) h*x)=
      (Real.fourierChar (tracePair (residueRepresentative c x:ℂ)
        ((h:ℂ)/((c:ℂ)*traceLambda))):ℂ) := by
  have he : Ideal.Quotient.mk (modulus c) h*x=
      Ideal.Quotient.mk (modulus c) (h*residueRepresentative c x) := by
    rw [map_mul,residueRepresentative_spec]
  rw [he,residueFourierChar_mk]
  congr 2
  unfold tracePair
  congr 2
  push_cast
  ring

theorem cubicThetaEisensteinGaussCoefficient_fourier {c : Eisenstein} (hc : c≠0)
    (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient c h=
      ∑' x : Residues (3*c), cubicThetaEisensteinWeight c (residueRepresentative (3*c) x)*
        residueFourierChar (3*c) (mul_ne_zero (by norm_num) hc)
          (Ideal.Quotient.mk (modulus (3*c)) h*x) := by
  unfold cubicThetaEisensteinGaussCoefficient cubicThetaEisensteinResidueWeight
  apply tsum_congr
  intro x
  rw [residueFourierChar_mk_mul]

theorem cubicThetaEisensteinGaussCoefficient_fourier_of_eq {q c : Eisenstein}
    (hc : c≠0) (hq : q≠0) (he : q=3*c) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient c h=
      ∑' x : Residues q, cubicThetaEisensteinWeight c (residueRepresentative q x)*
        residueFourierChar q hq (Ideal.Quotient.mk (modulus q) h*x) := by
  subst q
  exact cubicThetaEisensteinGaussCoefficient_fourier hc h

end CubicFirstMoment

end

end OAI
