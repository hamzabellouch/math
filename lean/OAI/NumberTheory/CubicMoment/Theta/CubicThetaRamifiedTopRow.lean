import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPhaseTransport

namespace OAI

/-! Exact scale of the top surviving ramified row at the theta pole. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaRamifiedTopScale :
    (81:ℂ)*(81:ℂ)^(-(4/3:ℂ))=(1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)) := by
  have hp : (81:ℂ)^(-(4/3:ℂ))=(3:ℂ)^(-(16/3:ℂ)) := by
    rw [show (81:ℂ)=((3:ℕ):ℂ)^4 by norm_num,←Complex.natCast_cpow_natCast_mul]
    congr 1
    norm_num
  calc
    _ = (3:ℂ)^(4:ℂ)*(3:ℂ)^(-(16/3:ℂ)) := by rw [hp]; norm_num [Complex.cpow_natCast]
    _ = (3:ℂ)^(-(4/3:ℂ)) := by rw [←Complex.cpow_add _ _ (by norm_num)]; congr 1; norm_num
    _ = (3:ℂ)^(-(1:ℂ))*(3:ℂ)^(-(1/3:ℂ)) := by
      rw [←Complex.cpow_add _ _ (by norm_num)]
      congr 1
      norm_num
    _ = _ := by rw [Complex.cpow_neg,Complex.cpow_one]; norm_num

lemma cubicThetaRamifiedTopFactor_eq (e : Eisensteinˣ) (r : Fin 3)
    (he : (e:Eisenstein)=omegaE^(r:ℕ) ∨ (e:Eisenstein)=-(omegaE^(r:ℕ)))
    (h : Eisenstein) :
    cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*h)=
      if (3:Eisenstein)∣-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+2+lambdaE*(r:ℕ) then
        ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*
          cubicThetaNinePhase (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h)
      else 0 := by
  rw [cubicThetaRamifiedFactor_value e r he 2 (4/3) h]
  norm_num only [Nat.reduceAdd,Nat.reduceMod,Nat.cast_one,mul_one]
  change (9*(if (3:Eisenstein)∣-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+2+lambdaE*(r:ℕ) then
    9*cubicThetaNinePhase (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h) else 0))*
      (81:ℂ)^(-(4/3:ℂ))=_
  split_ifs
  · calc
      _ = ((81:ℂ)*(81:ℂ)^(-(4/3:ℂ)))*
          cubicThetaNinePhase (-(((e⁻¹:Eisensteinˣ):Eisenstein))*h) := by ring
      _ = _ := by rw [cubicThetaRamifiedTopScale]
  · ring

lemma cubicThetaRamifiedTopFactor_positive_zero (e : Eisensteinˣ) {h : Eisenstein}
    (hh : lambdaE∣h-1) (he : lambdaE∣(e:Eisenstein)-1) :
    cubicThetaRamifiedFactor e 2 (4/3) (lambdaE^2*h)=0 := by
  obtain ⟨r,hr⟩ := cubicThetaUnit_signed_power e
  rw [cubicThetaRamifiedTopFactor_eq e r hr h]
  apply ite_eq_right
  intro hd
  have h3 : lambdaE∣(3:Eisenstein) := ⟨-lambdaE,by rw [mul_neg,←pow_two,lambdaE_sq]; ring⟩
  have ht := dvd_mul_of_dvd_right (h3.trans hd) (e:Eisenstein)
  have hi : (e:Eisenstein)*((e⁻¹:Eisensteinˣ):Eisenstein)=1 := by simp
  have hu : lambdaE∣-h+2*(e:Eisenstein) := by
    have heq : (e:Eisenstein)*(-(((e⁻¹:Eisensteinˣ):Eisenstein))*h+2+lambdaE*(r:ℕ))=
        -h+2*(e:Eisenstein)+lambdaE*((e:Eisenstein)*(r:ℕ)) := by
      linear_combination -h*hi
    rw [heq] at ht
    convert dvd_sub ht (dvd_mul_right lambdaE ((e:Eisenstein)*(r:ℕ))) using 1
    ring
  have h1 : lambdaE∣(1:Eisenstein) := by
    convert dvd_sub (dvd_add hu hh) (dvd_mul_of_dvd_right he (2:Eisenstein)) using 1
    ring
  exact lambdaE_prime.not_isUnit (isUnit_of_dvd_one h1)

end CubicFirstMoment

end

end OAI
