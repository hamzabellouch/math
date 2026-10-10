import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeInflation

namespace OAI

/-! The cube-modulus Ramanujan value at the missing square class.
This is a finite character identity, independent of its later Hecke application. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeRoot_ramanujan {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=-(norm p:ℂ)^2 := by
  have he := cubicThetaLocalPrimePowerGauss_reduction hp 2 h
  change cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=
    (norm (p^2):ℂ)*cubicThetaPrimeFourier p hp 3 h at he
  rw [cubicThetaPrimeFourier_three hp h,ite_eq_right hh] at he
  rw [he,eisenstein_norm_pow,Complex.ofReal_pow]
  ring

theorem cubicThetaPrimeCubeRoot_square_cancellation {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    1+(norm p:ℂ)⁻¹^2*cubicThetaLocalPrimePowerGauss p hp.2.ne_zero 3 (p^2*h)=0 := by
  rw [cubicThetaPrimeCubeRoot_ramanujan hp h hh]
  field_simp [Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne']
  ring

end CubicFirstMoment

end

end OAI
