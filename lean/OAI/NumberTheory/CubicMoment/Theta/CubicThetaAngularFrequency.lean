import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularPowers

namespace OAI

/-! The signed angular multipliers are precisely powers of the actual
complex Fourier frequency and its conjugate. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_div_nine (n : Eisenstein) :
    cubicThetaFrequency n=(n:ℂ)/9 := by
  have hs : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun n : Eisenstein => (n:ℂ)) lambdaE_sq
    push_cast at he
    rw [lambdaE_coe] at he
    convert he using 1
  have h4 : traceLambda^4=(9:ℂ) := by
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = _ := by rw [hs]; norm_num
  simp only [cubicThetaFrequency,h4]

lemma cubicThetaFrequency_phase (n : Eisenstein) :
    (‖cubicThetaFrequency n‖:ℂ)*((n:ℂ)/(‖(n:ℂ)‖:ℂ))=cubicThetaFrequency n := by
  simp only [cubicThetaFrequency_div_nine]
  by_cases hn : (n:ℂ)=0
  · simp [hn]
  · have hnorm : (‖(n:ℂ)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn)
    simp only [norm_div,Complex.norm_ofNat]
    push_cast
    field_simp [hnorm]

lemma cubicThetaFrequency_conj_phase (n : Eisenstein) :
    (‖cubicThetaFrequency n‖:ℂ)*((n:ℂ)/(‖(n:ℂ)‖:ℂ))⁻¹=
      star (cubicThetaFrequency n) := by
  by_cases hn : (n:ℂ)=0
  · simp [cubicThetaFrequency_div_nine,hn]
  have hnorm : (‖(n:ℂ)‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn)
  have hs : (n:ℂ)*star (n:ℂ)=(‖(n:ℂ)‖:ℂ)^2 := by
    simpa only [Complex.star_def] using Complex.mul_conj' (n:ℂ)
  simp only [cubicThetaFrequency_div_nine,norm_div,Complex.norm_ofNat,
    star_div₀,star_ofNat,inv_div]
  push_cast
  field_simp
  exact hs.symm

lemma cubicThetaAngularCoefficient_nat (a : Eisenstein → ℂ) (k : ℕ) (n : Eisenstein) :
    cubicThetaAngularCoefficient a (k:ℤ) n=cubicThetaFrequency n^k*a n := by
  simp only [cubicThetaAngularCoefficient,Int.natAbs_natCast,theta,zpow_natCast]
  rw [←mul_pow,cubicThetaFrequency_phase]

lemma cubicThetaAngularCoefficient_neg_nat (a : Eisenstein → ℂ) (k : ℕ) (n : Eisenstein) :
    cubicThetaAngularCoefficient a (-(k:ℤ)) n=star (cubicThetaFrequency n)^k*a n := by
  simp only [cubicThetaAngularCoefficient,Int.natAbs_neg,Int.natAbs_natCast,theta,
    zpow_neg,zpow_natCast,←inv_pow]
  rw [←mul_pow,cubicThetaFrequency_conj_phase]

lemma cubicThetaAngularCoefficient_nat_succ (a : Eisenstein → ℂ) (k : ℕ) (n : Eisenstein) :
    cubicThetaAngularCoefficient a ((k+1:ℕ):ℤ) n=
      cubicThetaFrequency n*cubicThetaAngularCoefficient a (k:ℤ) n := by
  rw [cubicThetaAngularCoefficient_nat,cubicThetaAngularCoefficient_nat,pow_succ]
  ring

lemma cubicThetaAngularCoefficient_neg_nat_succ (a : Eisenstein → ℂ) (k : ℕ) (n : Eisenstein) :
    cubicThetaAngularCoefficient a (-((k+1:ℕ):ℤ)) n=
      star (cubicThetaFrequency n)*cubicThetaAngularCoefficient a (-(k:ℤ)) n := by
  rw [cubicThetaAngularCoefficient_neg_nat,cubicThetaAngularCoefficient_neg_nat,pow_succ]
  ring

end CubicFirstMoment

end

end OAI
