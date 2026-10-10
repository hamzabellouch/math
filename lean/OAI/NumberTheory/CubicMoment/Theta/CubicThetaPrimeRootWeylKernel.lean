import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKloostermanCRT

namespace OAI

/-! Identify the actual Weyl Fourier row with the previously constructed
finite Kloosterman kernel, retaining the inverse-nine twist and zero extension. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

def cubicThetaPrimeRootWeylKernel {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues p) : ℂ :=
  ∑' r : Residues p,star (residueFourierChar p hp.2.ne_zero (k*r))*cubicResidueChar p hp r*
    residueFourierChar p hp.2.ne_zero (-(j*cubicThetaPrimeRootReciprocal p r))

theorem cubicThetaPrimeRootWeylKernel_kloosterman {p : Eisenstein} (hp : primaryPrime p)
    (j k : Residues p) :
    cubicThetaPrimeRootWeylKernel hp j k=
      cubicThetaSymbolKloosterman p hp.2.ne_zero (-k)
        (-j*Ring.inverse (Ideal.Quotient.mk (modulus p) 9)) := by
  unfold cubicThetaPrimeRootWeylKernel cubicThetaSymbolKloosterman
  apply tsum_congr
  intro r
  have hc : cubicSymbol p (residueRepresentative p r)=cubicResidueChar p hp r := by
    rw [cubicSymbol_prime hp,←cubicResidueChar_mk p hp,residueRepresentative_spec]
  rw [hc,cubicThetaResidueFourier_star]
  calc
    _ = cubicResidueChar p hp r*
        (residueFourierChar p hp.2.ne_zero (-(k*r))*
          residueFourierChar p hp.2.ne_zero (-(j*cubicThetaPrimeRootReciprocal p r))) := by ring
    _ = _ := by
      rw [←AddChar.map_add_eq_mul]
      congr 2
      rw [cubicThetaPrimeRootReciprocal,Ring.inverse_mul (Or.inl (cubicThetaPrimeRoot_nine_unit hp))]
      ring

end CubicFirstMoment

end

end OAI
