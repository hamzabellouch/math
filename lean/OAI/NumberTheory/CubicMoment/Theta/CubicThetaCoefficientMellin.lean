import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularMellin

namespace OAI

/-! Initial Mellin identity for the actual selected and projected
coefficient families, with their horizontal phases retained. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaCoefficientTwist (a : Eisenstein→ℂ) (z : ℂ) (n : Eisenstein) : ℂ :=
  a n*(Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ)

lemma cubicThetaCoefficientTwist_norm (a : Eisenstein→ℂ) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaCoefficientTwist a z n‖=‖a n‖ := by
  simp only [cubicThetaCoefficientTwist,norm_mul,Circle.norm_coe,mul_one]

lemma cubicThetaCoefficientTwist_angular_series (a : Eisenstein→ℂ) (z : ℂ) (v : ℝ) (ℓ : ℤ) :
    cubicThetaNonconstant (cubicThetaAngularCoefficient (cubicThetaCoefficientTwist a z) ℓ) (0,v)=
      cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v) := by
  classical
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,hn,ite_true]
  · simp only [cubicThetaSeriesTerm,hn,ite_false,cubicThetaCoefficientTwist,
      cubicThetaAngularCoefficient,tracePair,mul_zero,Complex.zero_re,
      AddChar.map_zero_eq_one,Circle.coe_one,mul_one]
    ring

theorem cubicThetaCoefficient_mellin {a : Eisenstein→ℂ} {C : ℝ}
    (hC : 0≤C) (ha : ∀ n,‖a n‖≤C) (z : ℂ) (ℓ : ℤ) {s : ℂ} (hs : 3/2<s.re) :
    mellin (fun v : ℝ => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,v))
      (2*s+(ℓ.natAbs:ℂ)-1)=
      (1/4:ℂ)*((2*Real.pi:ℝ):ℂ)^(-2*(s+(ℓ.natAbs:ℂ)/2))*
        Complex.Gamma (s+(ℓ.natAbs:ℂ)/2+1/6)*Complex.Gamma (s+(ℓ.natAbs:ℂ)/2-1/6)*
          cubicThetaDirichlet (fun n => theta ℓ n*cubicThetaCoefficientTwist a z n) (2*s-1) := by
  simp_rw [←cubicThetaCoefficientTwist_angular_series a z]
  exact cubicThetaAngular_completed hC
    (fun n => (cubicThetaCoefficientTwist_norm a z n).trans_le (ha n)) ℓ hs

end CubicFirstMoment

end

end OAI
