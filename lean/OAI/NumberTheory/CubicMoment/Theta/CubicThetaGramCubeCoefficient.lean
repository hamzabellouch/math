import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramCubeInflation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeValuation

namespace OAI

/-! The common-cube multiplier for every actual denominator, with the
smaller coefficient at denominators prime to the selected prime. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaKloostermanSum_cube_divisible {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0) (hpd : p∣d)
    (h k : Eisenstein) :
    cubicThetaKloostermanSum (p^3*h) (p^3*k) (p^3*d)
      (dvd_mul_of_dvd_right hd (p^3))=
      (norm (p^3):ℂ)*cubicThetaKloostermanSum h k d hd := by
  obtain ⟨m,e,hpe,he⟩ := WfDvdMonoid.max_power_factor hd0 hp.2.irreducible
  have he0 : e≠0 := (mul_ne_zero_iff.mp (he ▸ hd0)).2
  have h3p : IsCoprime (3:Eisenstein) p :=
    isCoprime_of_residue_isUnit (unit_residue_of_dvd_primary hp.1 (dvd_refl p))
  have he3 : (3:Eisenstein)∣e := h3p.pow_right.dvd_of_dvd_mul_left (he ▸ hd)
  cases m with
  | zero =>
    have hx := hpd
    rw [he,pow_zero,one_mul] at hx
    exact (hpe hx).elim
  | succ n =>
    have hprod : p^3*d=p^(n+4)*e := by rw [he,pow_add]; ring
    have H := cubicThetaKloostermanSum_cubeInflation hp he3 he0
      (hp.2.coprime_iff_not_dvd.mpr hpe).symm n h k
    simpa only [←hprod,←he] using H

theorem cubicThetaKloostermanSum_cube_multiplier {p d : Eisenstein}
    (hp : primaryPrime p) (hd : (3:Eisenstein)∣d) (hd0 : d≠0)
    (h k : Eisenstein) :
    cubicThetaKloostermanSum (p^3*h) (p^3*k) (p^3*d)
      (dvd_mul_of_dvd_right hd (p^3))=
      ((norm (p^3):ℂ)-(if p∣d then 0 else (norm (p^2):ℂ)))*
        cubicThetaKloostermanSum h k d hd := by
  by_cases hpd : p∣d
  · rw [ite_eq_left hpd,sub_zero,cubicThetaKloostermanSum_cube_divisible hp hd hd0 hpd]
  · rw [ite_eq_right hpd,cubicThetaKloostermanSum_cube_layer_three hp hd hd0
      (hp.2.coprime_iff_not_dvd.mpr hpd).symm]
    rw [eisenstein_norm_pow,eisenstein_norm_pow,Complex.ofReal_pow,Complex.ofReal_pow]
    ring

end CubicFirstMoment

end

end OAI
