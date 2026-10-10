import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCriticalMatrix
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeFreeSystem

namespace OAI

/-! Match the critical finite Gauss factors with the exact Euler factors
of the constructed arithmetic Fourier family. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCriticalScale (p : Eisenstein) : ℂ :=
  (norm p:ℂ)^(-(1/3:ℂ))

lemma cubicThetaPrimeCriticalScale_ne_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCriticalScale p≠0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne')

lemma cubicThetaPrimeFirstFactor_critical {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeFirstFactor p (4/3) h=
      (cubicThetaPrimeAdditiveGauss p hp 1 h/(norm p:ℂ))*cubicThetaPrimeCriticalScale p := by
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have he : (norm p:ℂ)^(-(4/3:ℂ))=(norm p:ℂ)⁻¹*cubicThetaPrimeCriticalScale p := by
    unfold cubicThetaPrimeCriticalScale
    rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ hq]
    congr 1
    norm_num
  rw [cubicThetaPrimeFirstFactor,cubicThetaPrimeAdditiveGauss_one hp h hh,he]
  ring

lemma cubicThetaPrimeSecondFactor_critical {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : IsCoprime p h) :
    cubicThetaPrimeCriticalScale p*cubicThetaPrimeSecondFactor p (4/3) h=
      cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ)^2 := by
  have hq : (norm p:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hp.2.ne_zero).ne'
  have he : cubicThetaPrimeCriticalScale p*((norm p:ℂ)^(-(4/3:ℂ)))^2=
      ((norm p:ℂ)^3)⁻¹ := by
    unfold cubicThetaPrimeCriticalScale
    rw [←Complex.cpow_mul_nat,←Complex.cpow_add _ _ hq]
    norm_num only [show (-(1/3:ℂ)+(-(4/3:ℂ))*(2:ℕ))=-(3:ℂ) by norm_num]
    rw [Complex.cpow_neg]
    norm_num
  have hs : star (Real.sqrt (norm p):ℂ)=(Real.sqrt (norm p):ℂ) := by simp
  rw [cubicThetaPrimeAdditiveGauss_two hp h hh,cubicThetaPrimeAdditiveGauss_one hp h hh,
    star_mul,star_mul,star_star,hs,cubicThetaPrimeSecondFactor]
  calc
    _ = ((norm p:ℂ)*cubicSymbol p h*(Real.sqrt (norm p):ℂ)*star (gauss p))*
        (cubicThetaPrimeCriticalScale p*((norm p:ℂ)^(-(4/3:ℂ)))^2) := by ring
    _ = _ := by rw [he]; field_simp

lemma cubicThetaRegularizedFrequency_primeFree_shift {p : Eisenstein}
    (hp : primaryPrime p) (h : Eisenstein) (hh : ¬p∣h) {s : ℂ} (hs : 1<s.re) :
    cubicThetaRegularizedFrequency (p*h) s=
      cubicThetaPrimeSecondFactor p s h*cubicThetaRegularizedPrimeFreeZero p h s+
        cubicThetaRegularizedPrimeFreeTwo p h s := by
  unfold cubicThetaRegularizedPrimeFreeZero cubicThetaRegularizedPrimeFreeTwo
  have hd := cubicThetaPrimeDeterminant_ne_zero hp hs
  have he := cubicThetaPrimeFactors_product hp s h hh
  rw [←mul_div_assoc,←add_div]
  apply (eq_div_iff hd).mpr
  unfold cubicThetaPrimeDeterminant
  linear_combination cubicThetaRegularizedFrequency (p*h) s*he

end CubicFirstMoment

end

end OAI
