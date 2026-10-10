import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFourierKernel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeAdditiveGauss

namespace OAI

/-! The branch Gauss multiplier in the original arithmetic additive
normalization. The factor at three cancels the inverse different. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeFirstFourier_additive {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicSymbol p 3*cubicThetaPrimeFourier p hp 1 h=
      cubicThetaPrimeAdditiveGauss p hp 1 h := by
  rw [cubicThetaPrimeFourier_unit hp (by decide) h hh,pow_one,
    cubicThetaPrimeFourier_one_one hp,cubicThetaPrimeAdditiveGauss_one hp h hh]
  calc
    _ = (cubicSymbol p 3*cubicSymbol p lambdaE)*
        (star (cubicSymbol p h)*(Real.sqrt (norm p):ℂ)*gauss p) := by ring
    _ = _ := by rw [←cubicSymbol_mul_upper hp.1,cubicSymbol_three_lambda hp.1,one_mul]

theorem cubicThetaPrimeCubeFirstFourier_quotient {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeCubeUnitFourier hp 1 (p*h)/(norm p:ℂ)=
      cubicThetaPrimeAdditiveGauss p hp 1 h := by
  have he := cubicThetaPrimeCubeUnitFourier_reduction hp 1 (by decide) h
  simp only [Fin.val_one,Nat.reduceSub,pow_one] at he
  rw [he]
  have hn : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  calc
    _ = cubicSymbol p 3*cubicThetaPrimeFourier p hp 1 h := by field_simp
    _ = _ := cubicThetaPrimeCubeFirstFourier_additive hp h hh

end CubicFirstMoment

end

end OAI
