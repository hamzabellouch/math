import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeReductionPhase

namespace OAI

/-! Actual hyperbolic coordinates of the triangularized cubed-prime
branches; the horizontal translation is retained exactly. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaPrimeCubeReducedMatrix_mobius {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (n : Eisenstein) (hn : ¬p∣n) (z : ℂ × ℝ) :
    cubicThetaMobius (cubicThetaPrimeCubeReducedMatrix hp k n hn) z=
      ((cubicThetaPrimeCubeReducedScale hp k)⁻¹^2*z.1+
        ((((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)/
          cubicThetaPrimeSquareRoot (p^3))/cubicThetaPrimeCubeReducedScale hp k,
        z.2/Complex.normSq (cubicThetaPrimeCubeReducedScale hp k)) := by
  let t := cubicThetaPrimeCubeReducedScale hp k
  let b := (((cubicThetaPrimeCubeReduction hp k n hn).val 0 1:Eisenstein):ℂ)/
    cubicThetaPrimeSquareRoot (p^3)
  have ht : t≠0 := cubicThetaPrimeCubeReducedScale_ne_zero hp k
  have hts : star t≠0 := star_ne_zero.mpr ht
  have hden : cubicThetaMobiusDenominator (cubicThetaPrimeCubeReducedMatrix hp k n hn) z=
      Complex.normSq t := by
    simp [cubicThetaMobiusDenominator,cubicThetaPrimeCubeReducedMatrix_c,
      cubicThetaPrimeCubeReducedMatrix_d,t]
  have hnum : cubicThetaMobiusNumerator (cubicThetaPrimeCubeReducedMatrix hp k n hn) z=
      (t⁻¹*z.1+b)*star t := by
    simp [cubicThetaMobiusNumerator,cubicThetaPrimeCubeReducedMatrix_c,
      cubicThetaPrimeCubeReducedMatrix_d,cubicThetaPrimeCubeReducedMatrix_a,
      cubicThetaPrimeCubeReducedMatrix_b,t,b]
  apply Prod.ext
  · change cubicThetaMobiusNumerator _ z/(cubicThetaMobiusDenominator _ z:ℂ)=t⁻¹^2*z.1+b/t
    rw [hnum,hden,show (Complex.normSq t:ℂ)=t*star t from (Complex.mul_conj t).symm]
    field_simp
  · change z.2/cubicThetaMobiusDenominator _ z=z.2/Complex.normSq t
    rw [hden]

lemma cubicThetaPrimeCubeReducedScale_square {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) :
    (cubicThetaPrimeCubeReducedScale hp k)⁻¹^2=(p:ℂ)^k.val/(p:ℂ)^(3-k.val) := by
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  have hs : (cubicThetaPrimeSquareRoot (p^3))^2=(p:ℂ)^3 :=
    (cubicThetaPrimeSquareRoot_sq (p^3)).trans
      (map_pow (eisensteinRing.subtype : Eisenstein →+* ℂ) p 3)
  have he : (p:ℂ)^(3-k.val)*(p:ℂ)^k.val=(p:ℂ)^3 := by
    rw [←pow_add]
    congr 1
    omega
  unfold cubicThetaPrimeCubeReducedScale
  rw [inv_div,div_pow,hs,←he]
  field_simp

lemma cubicThetaPrimeCubeReducedScale_translation {p : Eisenstein} (hp : primaryPrime p)
    (k : Fin 3) (b : ℂ) :
    (b/cubicThetaPrimeSquareRoot (p^3))/cubicThetaPrimeCubeReducedScale hp k=
      b/(p:ℂ)^(3-k.val) := by
  have hq := cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  unfold cubicThetaPrimeCubeReducedScale
  field_simp

end CubicFirstMoment

end

end OAI
