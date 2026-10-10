import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeFourierOperator
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLocalCases

namespace OAI

/-! On the zero horizontal mode both nontrivial cubic characters cancel.
The remaining two height terms give the literal spherical multiplier. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeGauss_zeroFrequency {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) : cubicThetaPrimeCubeFiniteGauss hp k 0=0 := by
  have ht := cubicThetaPrimeCubeFiniteGauss_reduction hp k 0
  rw [mul_zero] at ht
  have hz : cubicThetaPrimeFourier p hp k.val 0=0 := by
    have he : k.val=1 ∨ k.val=2 := by have := k.isLt; omega
    rcases he with he | he
    · rw [he]
      simpa only [mul_zero] using cubicThetaPrimeFourier_one_multiple hp 0
    · rw [he]
      simpa only [mul_zero] using cubicThetaPrimeFourier_two_multiple hp 0
  rw [ht,hz,mul_zero]

lemma cubicThetaPrimeCubeUnitFourier_zeroFrequency {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (hk : k.val≠0) : cubicThetaPrimeCubeUnitFourier hp k 0=0 := by
  rw [cubicThetaPrimeCubeUnitFourier_eq hp k hk,cubicThetaPrimeCubeGauss_zeroFrequency hp k hk,
    mul_zero]

lemma cubicThetaPrimeCubeFourierMode_zero (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFourierMode 0 f x=f x.val.2 := by
  simp [cubicThetaPrimeCubeFourierMode,cubicThetaRowFrequency,tracePair]

lemma cubicThetaPrimeCubeScaledMode_zero {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeScaledMode hp k 0 f x=
      f ((‖(p:ℂ)‖^k.val/‖(p:ℂ)‖^(3-k.val))*x.val.2) := by
  simp [cubicThetaPrimeCubeScaledMode,cubicThetaRowFrequency,tracePair]

theorem cubicThetaPrimeCubeFunctionOperator_height {p : Eisenstein} (hp : primaryPrime p)
    (f : ℝ → ℂ) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeFunctionOperator hp (fun y => f y.val.2) x=
      f (‖(p:ℂ)‖^3*x.val.2)+(norm (p^3):ℂ)*f ((1/‖(p:ℂ)‖^3)*x.val.2) := by
  have he := cubicThetaPrimeCubeFunctionOperator_mode hp 0 f x
  have hF : cubicThetaPrimeCubeFourierMode 0 f=(fun y => f y.val.2) :=
    funext (cubicThetaPrimeCubeFourierMode_zero f)
  rw [hF,cubicThetaPrimeCubeUnitFourier_zeroFrequency hp 1 (by decide),
    cubicThetaPrimeCubeUnitFourier_zeroFrequency hp (⟨2,by decide⟩ : Fin 3) (by decide),
    zero_mul,zero_mul,add_zero,add_zero,cubicThetaPrimeCubeBottomFourier_eq] at he
  simp only [dvd_zero,ite_true] at he
  rw [cubicThetaPrimeCubeScaledMode_zero] at he
  have hd : (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x).val.2=
      ‖(p:ℂ)‖^3*x.val.2 := by
    change (cubicThetaMobius (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) x.val).2=_
    rw [cubicThetaMobius_primeDilation]
    simp only [Subalgebra.coe_pow,norm_pow]
  simpa only [hd,Fin.val_zero,Nat.sub_zero,pow_zero] using he

end CubicFirstMoment

end

end OAI
