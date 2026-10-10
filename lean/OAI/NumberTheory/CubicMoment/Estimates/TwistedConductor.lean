import OAI.NumberTheory.CubicMoment.Estimates.ConductorLocal
import OAI.NumberTheory.CubicMoment.Estimates.ResidueProducts

namespace OAI

/-! The variable squarefree conductor survives multiplication by a fixed
character of coprime small modulus. Detection is by explicit local CRT. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem twisted_conductor_left_prime {a b d p r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r) (hp : primaryPrime p) (hpa : p ∣ a)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) : p ∣ d := by
  by_contra hpd
  obtain ⟨c,rfl⟩ := hpa
  have hc : primary c := primary_of_mul hp.1 ha
  have hpc : IsCoprime p c := (IsRelPrime.of_squarefree_mul hsa).isCoprime
  have hpb : IsCoprime p b := hab.of_mul_left_left
  have hpd' : IsCoprime p d := hp.2.irreducible.coprime_iff_not_dvd.mpr hpd
  have hpr : IsCoprime p r := hsmall.of_mul_left_left.of_mul_left_left
  let Q := 3*c*b*d*r
  have hpQ : IsCoprime p Q :=
    ((((primary_coprime_three hp.1).mul_right hpc).mul_right hpb).mul_right hpd').mul_right hpr
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp (cubicResidueChar_ne_one hp)
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective (u : Residues p)
  obtain ⟨x,hxp,hxQ⟩ := residue_crt_one hpQ y
  have hx3 : (3:Eisenstein) ∣ x-1 := (show (3:Eisenstein) ∣ Q from ⟨c*b*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxc : c ∣ x-1 := (show c ∣ Q from ⟨3*b*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxb : b ∣ x-1 := (show b ∣ Q from ⟨3*c*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxd : d ∣ x-1 := (show d ∣ Q from ⟨3*c*b*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxr : r ∣ x-1 := (show r ∣ Q from ⟨3*c*b*d,by dsimp [Q]; ring⟩).trans hxQ
  have hrx := isCoprime_of_dvd_sub_one hxr
  have hη : η (Ideal.Quotient.mk (modulus r) x) = 1 := by
    rw [residue_eq_of_dvd_sub hxr,map_one,map_one]
  have hxp' : Ideal.Quotient.mk (modulus p) x = u :=
    (residue_eq_of_dvd_sub hxp).trans hy
  have hpx : IsCoprime p x := isCoprime_of_residue_isUnit (by rw [hxp']; exact u.isUnit)
  have hcx := isCoprime_of_dvd_sub_one hxc
  have hbx := isCoprime_of_dvd_sub_one hxb
  have hval := hagree x hx3 (((hpx.mul_left hcx).mul_left hbx).mul_left hrx)
  have hψ : ψ (Ideal.Quotient.mk (modulus d) x) = 1 := by
    rw [residue_eq_of_dvd_sub hxd,map_one,map_one]
  rw [hψ,hη,mul_one,mixedCubic,cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hc),
    cubicSymbol_eq_one_of_dvd_sub hc hxc,cubicSymbol_eq_one_of_dvd_sub hb hxb,
    star_one,mul_one,mul_one,cubicSymbol_prime hp,← cubicResidueChar_mk p hp,hxp'] at hval
  exact hu hval.symm


theorem twisted_conductor_contains {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) :
    a*b ∣ d := by
  have had : a ∣ d := squarefree_primary_dvd_of_prime_dvd ha hsa
    (fun p hp hpa => twisted_conductor_left_prime ha hb hsa hab hsmall hp hpa ψ η hagree)
  have hswap : ∀ x : Eisenstein, primary x → IsCoprime (b*a*r) x →
      (star ψ) (Ideal.Quotient.mk (modulus d) x) =
        mixedCubic b a x*(star η) (Ideal.Quotient.mk (modulus r) x) := by
    intro x hx hcop
    rw [MulChar.star_apply,hagree x hx (by simpa only [mul_comm] using hcop)]
    simp only [mixedCubic,star_mul,star_star,MulChar.star_apply]
    ring
  have hbd : b ∣ d := squarefree_primary_dvd_of_prime_dvd hb hsb
    (fun p hp hpb => twisted_conductor_left_prime hb ha hsb hab.symm
      (by simpa only [mul_comm] using hsmall) hp hpb (star ψ) (star η) hswap)
  exact hab.isRelPrime.mul_dvd had hbd

end CubicFirstMoment

end

end OAI
