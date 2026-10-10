import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedLowRow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGaussParity

namespace OAI

/-! The two unit classes which survive in the middle ramified row. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaEisensteinGaussCoefficient_middle_one (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (lambdaE^3) (lambdaE^3*h)=
      27*residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) h) := by
  have he := cubicThetaEisensteinGaussCoefficient_ramified_value 1 (lambdaE^2*h)
  have hp : lambdaE*(lambdaE^2*h)=lambdaE^3*h := by ring
  have hx : -(lambdaE^2*h)=3*h := by rw [lambdaE_sq]; ring
  have hd : (3:Eisenstein) ∣ 3*h := dvd_mul_right _ _
  have hφ := cubicThetaFourier_nine_triple h 1
  simp only [mul_one] at hφ
  norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_zero,mul_zero,add_zero,
    pow_one,cubicThetaNorm_lambda_pow] at he
  rw [hp,hx,ite_eq_left hd,hφ] at he
  have hn : norm lambdaE=3 := by simpa only [pow_one] using cubicThetaNorm_lambda_pow 1
  rw [hn] at he
  convert he using 1
  push_cast
  ring

theorem cubicThetaEisensteinGaussCoefficient_middle_neg_one (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient (-lambdaE^3) (lambdaE^3*h)=
      27*residueFourierChar 3 (by norm_num) (Ideal.Quotient.mk (modulus 3) (-h)) := by
  have h3 : (3:Eisenstein) ∣ lambdaE^3 := by
    refine ⟨-lambdaE,?_⟩
    rw [pow_succ,lambdaE_sq]
    ring
  have he := cubicThetaEisensteinGaussCoefficient_neg h3
    (pow_ne_zero _ lambdaE_prime.ne_zero) (-(lambdaE^3*h))
  rw [neg_neg] at he
  rw [he,show -(lambdaE^3*h)=lambdaE^3*(-h) by ring,
    cubicThetaEisensteinGaussCoefficient_middle_one]

theorem cubicThetaEisensteinGaussCoefficient_middle_other (e : Eisensteinˣ)
    (hpos : e≠1) (hneg : e≠-1) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE^3*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  have hr0 : (r:ℕ)≠0 := by
    intro hz
    simp only [hz,pow_zero] at hr
    rcases hr with hr | hr
    · exact hpos (Units.ext hr)
    · exact hneg (Units.ext hr)
  have hn : ¬(3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE^2*h)+
      2*(((1+2)%3:ℕ):Eisenstein)+lambdaE*(r:ℕ) := by
    intro hd
    norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_zero,mul_zero,add_zero] at hd
    have ht : (3:Eisenstein) ∣ -(((e⁻¹:Eisensteinˣ):Eisenstein))*(lambdaE^2*h) := by
      refine ⟨((e⁻¹:Eisensteinˣ):Eisenstein)*h,?_⟩
      rw [lambdaE_sq]
      ring
    have hd' : (3:Eisenstein) ∣ lambdaE*(r:ℕ) := by
      simpa only [add_sub_cancel_left] using dvd_sub hd ht
    obtain ⟨a,ha⟩ := hd'
    have hlam : lambdaE ∣ ((r:ℕ):Eisenstein) := by
      refine ⟨-a,?_⟩
      apply mul_left_cancel₀ lambdaE_prime.ne_zero
      calc
        lambdaE*(r:ℕ)=3*a := ha
        _ = lambdaE*(lambdaE*(-a)) := by
          have hs := lambdaE_sq
          linear_combination a*hs
    fin_cases r
    · exact hr0 rfl
    · have hu : lambdaE ∣ (1:Eisenstein) := by simpa using hlam
      exact lambdaE_prime.not_isUnit (isUnit_of_dvd_one hu)
    · exact lambdaE_prime.not_isUnit
        ((primary_coprime_lambda primary_neg_two).isRelPrime (dvd_neg.mpr hlam) dvd_rfl)
  have he := cubicThetaEisensteinGaussCoefficient_all_ramified e r hr 1 (lambdaE^2*h)
  simpa only [pow_one,show lambdaE*(lambdaE^2*h)=lambdaE^3*h by ring,
    ite_eq_right hn,mul_zero] using he

theorem cubicThetaEisensteinGaussCoefficient_middle (e : Eisensteinˣ) (h : Eisenstein) :
    cubicThetaEisensteinGaussCoefficient ((e:Eisenstein)*lambdaE^3) (lambdaE^3*h)=
      if e=1 then 27*residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) h)
      else if e=-1 then 27*residueFourierChar 3 (by norm_num)
        (Ideal.Quotient.mk (modulus 3) (-h)) else 0 := by
  split_ifs with hp hn
  · subst e
    simpa only [Units.val_one,one_mul] using cubicThetaEisensteinGaussCoefficient_middle_one h
  · subst e
    simpa only [Units.val_neg,Units.val_one,neg_one_mul] using
      cubicThetaEisensteinGaussCoefficient_middle_neg_one h
  · exact cubicThetaEisensteinGaussCoefficient_middle_other e hp hn h

end CubicFirstMoment

end

end OAI
