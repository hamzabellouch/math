import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDilation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinCusp

namespace OAI

/-! Explicit coordinates and the exact smaller cusp period of the
prime-dilated arithmetic Eisenstein family. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaMobius_primeDilation {p : Eisenstein} (hp : p≠0) (z : ℂ × ℝ) :
    cubicThetaMobius (cubicThetaPrimeDilation hp) z=
      ((p:ℂ)*z.1,‖(p:ℂ)‖*z.2) := by
  let q := cubicThetaPrimeSquareRoot p
  have hq : q≠0 := cubicThetaPrimeSquareRoot_ne_zero hp
  have hs : q^2=(p:ℂ) := cubicThetaPrimeSquareRoot_sq p
  have hqs : star q≠0 := star_ne_zero.mpr hq
  have hn : Complex.normSq q=‖(p:ℂ)‖ := by
    rw [Complex.normSq_eq_norm_sq]
    simpa only [norm_pow] using congrArg (fun z : ℂ => ‖z‖) hs
  have hnc : (Complex.normSq q:ℂ)=q*star q := (Complex.mul_conj q).symm
  have hden : cubicThetaMobiusDenominator (cubicThetaPrimeDilation hp) z=
      (Complex.normSq q)⁻¹ := by
    simp [cubicThetaMobiusDenominator,cubicThetaPrimeDilation,q]
  have hnum : cubicThetaMobiusNumerator (cubicThetaPrimeDilation hp) z=
      q*z.1*star (q⁻¹) := by
    simp [cubicThetaMobiusNumerator,cubicThetaPrimeDilation,q]
  apply Prod.ext
  · change cubicThetaMobiusNumerator _ z/(cubicThetaMobiusDenominator _ z:ℂ)=(p:ℂ)*z.1
    rw [hnum,hden,Complex.ofReal_inv,hnc,star_inv₀,←hs]
    field_simp
  · change z.2/cubicThetaMobiusDenominator _ z=_
    rw [hden,div_inv_eq_mul,hn]
    ring

theorem cubicThetaEisenstein_prime_small_period {p : Eisenstein} (hp : p≠0)
    (m : Eisenstein) {z : ℂ × ℝ} (hz : 0<z.2) (s : ℂ) :
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaPrimeDilation hp)
      (z.1+((3*m:Eisenstein):ℂ)/(p:ℂ),z.2)) s=
    cubicThetaEisenstein (cubicThetaMobius (cubicThetaPrimeDilation hp) z) s := by
  have hpC : (p:ℂ)≠0 := fun he => hp (Subtype.ext he)
  rw [cubicThetaMobius_primeDilation,cubicThetaMobius_primeDilation]
  have he : (p:ℂ)*(z.1+((3*m:Eisenstein):ℂ)/(p:ℂ))=
      (p:ℂ)*z.1+((3*m:Eisenstein):ℂ) := by field_simp
  rw [he]
  exact cubicThetaEisenstein_three_periodic m (p:=((p:ℂ)*z.1,‖(p:ℂ)‖*z.2))
    (mul_pos (norm_pos_iff.mpr hpC) hz) s

end CubicFirstMoment

end

end OAI
