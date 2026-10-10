import OAI.NumberTheory.CubicMoment.Estimates.PrimaryCharacterNonprincipal
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryIdealMoments
import OAI.NumberTheory.CubicMoment.Estimates.ResidueIdealCharacters

namespace OAI

/-! Local detection of the squarefree cubic conductor. A nontrivial
prime character survives every inducing modulus, as witnessed by CRT. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residue_crt_one {p Q : Eisenstein} (h : IsCoprime p Q) (y : Eisenstein) :
    ∃ x : Eisenstein, p ∣ x-y ∧ Q ∣ x-1 := by
  obtain ⟨u,v,huv⟩ := h
  refine ⟨p*u+Q*v*y,⟨u*(1-y),?_⟩,⟨v*(y-1),?_⟩⟩
  · linear_combination y*huv
  · linear_combination huv

lemma cubicSymbol_eq_one_of_dvd_sub {q x : Eisenstein}
    (hq : primary q) (hx : q ∣ x-1) : cubicSymbol q x = 1 := by
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub hx)]
  exact (cubic_reciprocity hq (by norm_num [primary])).trans (cubicSymbol_one_lower q)

lemma isCoprime_of_dvd_sub_one {q x : Eisenstein} (hx : q ∣ x-1) : IsCoprime q x := by
  apply isCoprime_of_residue_isUnit
  rw [residue_eq_of_dvd_sub hx,map_one]
  exact isUnit_one

/-- Every prime in the left squarefree cubic factor divides a modulus
whose character agrees with the mixed symbol on primary coprime inputs. -/
theorem mixed_conductor_left_prime {a b d p : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a)
    (hab : IsCoprime a b) (hp : primaryPrime p) (hpa : p ∣ a)
    (ψ : MulChar (Residues d) ℂ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x) : p ∣ d := by
  by_contra hpd
  obtain ⟨c,rfl⟩ := hpa
  have hc : primary c := primary_of_mul hp.1 ha
  have hpc : IsCoprime p c := (IsRelPrime.of_squarefree_mul hsa).isCoprime
  have hpb : IsCoprime p b := hab.of_mul_left_left
  have hpd' : IsCoprime p d := hp.2.irreducible.coprime_iff_not_dvd.mpr hpd
  let Q := 3*c*b*d
  have hpQ : IsCoprime p Q :=
    (((primary_coprime_three hp.1).mul_right hpc).mul_right hpb).mul_right hpd'
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp (cubicResidueChar_ne_one hp)
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective (u : Residues p)
  obtain ⟨x,hxp,hxQ⟩ := residue_crt_one hpQ y
  have hx3 : (3:Eisenstein) ∣ x-1 := (show (3:Eisenstein) ∣ Q from ⟨c*b*d,by dsimp [Q]; ring⟩).trans hxQ
  have hxc : c ∣ x-1 := (show c ∣ Q from ⟨3*b*d,by dsimp [Q]; ring⟩).trans hxQ
  have hxb : b ∣ x-1 := (show b ∣ Q from ⟨3*c*d,by dsimp [Q]; ring⟩).trans hxQ
  have hxd : d ∣ x-1 := (show d ∣ Q from ⟨3*c*b,by dsimp [Q]; ring⟩).trans hxQ
  have hxp' : Ideal.Quotient.mk (modulus p) x = u :=
    (residue_eq_of_dvd_sub hxp).trans hy
  have hpx : IsCoprime p x := isCoprime_of_residue_isUnit (by rw [hxp']; exact u.isUnit)
  have hcx := isCoprime_of_dvd_sub_one hxc
  have hbx := isCoprime_of_dvd_sub_one hxb
  have hval := hagree x hx3 ((hpx.mul_left hcx).mul_left hbx)
  have hψ : ψ (Ideal.Quotient.mk (modulus d) x) = 1 := by
    rw [residue_eq_of_dvd_sub hxd,map_one,map_one]
  rw [hψ,mixedCubic,cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hc),
    cubicSymbol_eq_one_of_dvd_sub hc hxc,cubicSymbol_eq_one_of_dvd_sub hb hxb,
    star_one,mul_one,mul_one,cubicSymbol_prime hp,← cubicResidueChar_mk p hp,hxp'] at hval
  exact hu hval.symm

lemma squarefree_primary_dvd_of_prime_dvd {a d : Eisenstein} (ha : primary a)
    (hsa : Squarefree a)
    (hprime : ∀ p : Eisenstein, primaryPrime p → p ∣ a → p ∣ d) : a ∣ d := by
  apply (primary_induction (P := fun a => Squarefree a →
    (∀ p : Eisenstein, primaryPrime p → p ∣ a → p ∣ d) → a ∣ d) ?_ ?_ ha) hsa hprime
  · intro _ _
    exact one_dvd d
  · intro p c hp hc ih hsf hall
    have hpd : p ∣ d := hall p hp (dvd_mul_right p c)
    have hcd : c ∣ d := ih hsf.of_mul_right (fun r hr hrc =>
      hall r hr (hrc.trans (dvd_mul_left c p)))
    exact (IsRelPrime.of_squarefree_mul hsf).mul_dvd hpd hcd

/-- The conductor away from three is exactly the original squarefree
product: no variable prime can disappear under primitive reduction. -/
theorem mixed_conductor_contains {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (ψ : MulChar (Residues d) ℂ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x) : a*b ∣ d := by
  have had : a ∣ d := squarefree_primary_dvd_of_prime_dvd ha hsa
    (fun p hp hpa => mixed_conductor_left_prime ha hb hsa hab hp hpa ψ hagree)
  have hswap : ∀ x : Eisenstein, primary x → IsCoprime (b*a) x →
      (star ψ) (Ideal.Quotient.mk (modulus d) x) = mixedCubic b a x := by
    intro x hx hcop
    rw [MulChar.star_apply,hagree x hx (by simpa only [mul_comm] using hcop)]
    simp only [mixedCubic,star_mul,star_star]
  have hbd : b ∣ d := squarefree_primary_dvd_of_prime_dvd hb hsb
    (fun p hp hpb => mixed_conductor_left_prime hb ha hsb hab.symm hp hpb (star ψ) hswap)
  exact hab.isRelPrime.mul_dvd had hbd

lemma mixed_character_primary_match {a b d x : Eisenstein}
    (ha : primary a) (hb : primary b) (ψ : MulChar (Residues d) ℂ)
    (hdiv : a*b ∣ d)
    (hagree : ∀ y : Eisenstein, primary y → IsCoprime (a*b) y →
      ψ (Ideal.Quotient.mk (modulus d) y) = mixedCubic a b y)
    (hx : primary x) : ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x := by
  by_cases hcop : IsCoprime (a*b) x
  · exact hagree x hx hcop
  · have hz : mixedCubic a b x = 0 := mixedCubic_eq_zero_of_nonunit ha hb x
      (fun h => hcop (isCoprime_of_residue_isUnit h))
    rw [hz]
    apply MulChar.map_nonunit
    intro h
    exact hcop ((isCoprime_of_residue_isUnit h).of_isCoprime_of_dvd_left hdiv)

lemma residueIdealChar_primaryNormalize {d : Eisenstein} (ψ : MulChar (Residues d) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (ν : EisensteinIdealExponent) :
    residueIdealChar d ψ ν = ψ (Ideal.Quotient.mk (modulus d) (idealPrimaryGenerator ν)) := by
  obtain ⟨u,hassoc⟩ := primaryNormalize_associated (idealExponentGenerator ν)
  change ψ (Ideal.Quotient.mk (modulus d) (idealExponentGenerator ν)) =
    ψ (Ideal.Quotient.mk (modulus d) (primaryNormalize (idealExponentGenerator ν)))
  rw [← hassoc,map_mul,map_mul,hu,mul_one]

/-- On all ideals prime to three, the primitive ideal coefficient agrees
with the actual mixed cubic coefficient, including their common zeros. -/
theorem primitive_ideal_mixed_match {a b d : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (ψ : MulChar (Residues d) ℂ)
    (hu : ∀ u : Eisensteinˣ, ψ (Ideal.Quotient.mk (modulus d) u) = 1)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x)
    (ν : EisensteinIdealExponent) (hν : primary (idealPrimaryGenerator ν)) :
    residueIdealChar d ψ ν = primaryMixedIdealChar a b ν := by
  rw [residueIdealChar_primaryNormalize ψ hu ν,
    mixed_character_primary_match ha hb ψ (mixed_conductor_contains ha hb hsa hsb hab ψ hagree) hagree hν,
    primaryMixedIdealChar_eq,ite_eq_left hν]

end CubicFirstMoment

end

end OAI
