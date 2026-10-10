import Mathlib
import OAI.NumberTheory.CubicGram.Jacobi

namespace OAI

/-! Finite-field Frobenius relations and distinct-character reciprocity. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable

noncomputable section
open scoped BigOperators
open AddChar MulChar
namespace CubicFirstMoment.ReciprocityKernel

lemma gaussSum_card_frobenius {F F' K : Type*}
    [Field F] [Fintype F] [Field F'] [Fintype F'] [Field K] [Algebra F' K]
    (χ : MulChar F F') (ψ : AddChar F K) :
    gaussSum (χ.ringHomComp (algebraMap F' K)) ψ ^ Fintype.card F' =
      gaussSum (χ.ringHomComp (algebraMap F' K)) (ψ.mulShift (Fintype.card F' : F)) := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F' (ringChar F')
  have he := Algebra.ringChar_eq F' K
  have : CharP K (ringChar F') := he.symm ▸ (inferInstance : CharP K (ringChar K))
  have : Fact (Nat.Prime (ringChar F')) := ⟨hp⟩
  have hsum : gaussSum (χ.ringHomComp (algebraMap F' K)) ψ ^ Fintype.card F' =
      ∑ x : F, ((algebraMap F' K) (χ x) * ψ x) ^ Fintype.card F' := by
    rw [hc, gaussSum, sum_pow_char_pow]
    rfl
  rw [hsum, gaussSum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_pow, ← map_pow, FiniteField.pow_card]
  congr 1
  rw [← AddChar.pow_apply, AddChar.pow_mulShift]

theorem cubic_jacobi_card_relation {F F' : Type*} [Field F] [Fintype F]
    [Field F'] [Fintype F'] (χ : MulChar F F')
    (hχ : χ ^ 3 = 1) (hχne : χ ≠ 1) (hminus : χ (-1) = 1)
    (hthree : 3 ∣ Fintype.card F' - 1)
    (hchar : ringChar F' ≠ ringChar F) :
    ((Fintype.card F : F') * jacobiSum χ χ) ^ ((Fintype.card F' - 1) / 3) *
      χ (Fintype.card F') = 1 := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  obtain ⟨n', hp', hc'⟩ := FiniteField.card F' (ringChar F')
  have : Fact (Nat.Prime (ringChar F)) := ⟨hp⟩
  have : Fact (Nat.Prime (ringChar F')) := ⟨hp'⟩
  have hunit : IsUnit (Fintype.card F' : F) := by
    rw [hc', Nat.cast_pow]
    apply IsUnit.pow
    apply (isUnit_iff_not_dvd_char F (ringChar F')).mpr
    exact (Nat.prime_dvd_prime_iff_eq hp' hp).not.mpr hchar
  have hN : (Fintype.card F : F') ≠ 0 := by
    rw [hc, Nat.cast_pow]
    apply pow_ne_zero
    apply IsUnit.ne_zero
    apply (isUnit_iff_not_dvd_char F' (ringChar F)).mpr
    exact (Nat.prime_dvd_prime_iff_eq hp hp').not.mpr hchar.symm
  let ψ := FiniteField.primitiveChar F F' hchar
  let K := CyclotomicField ψ.n F'
  let χ' := χ.ringHomComp (algebraMap F' K)
  have hχ' : χ' ^ 3 = 1 := by
    dsimp [χ']
    rw [ringHomComp_pow, hχ, ringHomComp_one]
  have hχ'ne : χ' ≠ 1 := (ringHomComp_ne_one_iff (RingHom.injective _)).mpr hχne
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf χ' = 3 := orderOf_eq_prime hχ' hχ'ne
  have hM : χ' (-1) = 1 := by
    change (algebraMap F' K) (χ (-1)) = 1
    rw [hminus, map_one]
  have hg := gaussSum_pow_eq_prod_jacobiSum (χ := χ') (ψ := ψ.char)
    (by rw [hord]; norm_num) ψ.prim
  rw [hord] at hg
  norm_num [hM, Finset.prod_Ico_succ_top] at hg
  have hNK : (Fintype.card F : K) ≠ 0 := by
    rw [← map_natCast (algebraMap F' K)]
    exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hN
  have hg0 := gaussSum_ne_zero_of_nontrivial hNK hχ'ne ψ.prim
  have hf := gaussSum_card_frobenius χ ψ.char
  change gaussSum χ' ψ.char ^ Fintype.card F' =
    gaussSum χ' (ψ.char.mulShift (Fintype.card F' : F)) at hf
  have hm := gaussSum_mulShift χ' ψ.char hunit.unit
  rw [hunit.unit_spec, ← hf] at hm
  have hsplit : Fintype.card F' = 3*((Fintype.card F' - 1)/3)+1 := by
    rw [Nat.mul_div_cancel' hthree, Nat.sub_add_cancel Fintype.card_pos]
  rw [hsplit, pow_add, pow_mul, pow_one, hg] at hm
  rw [← hsplit] at hm
  apply (algebraMap F' K).injective
  rw [map_one, map_mul, map_pow, map_mul, map_natCast, ← jacobiSum_ringHomComp]
  change ((Fintype.card F : K) * jacobiSum χ' χ') ^ ((Fintype.card F' - 1) / 3) *
    χ' (Fintype.card F') = 1
  apply mul_right_cancel₀ hg0
  calc
    _ = χ' (Fintype.card F') * (((Fintype.card F : K) * jacobiSum χ' χ') ^
        ((Fintype.card F' - 1) / 3) * gaussSum χ' ψ.char) := by ring
    _ = gaussSum χ' ψ.char := hm
    _ = 1 * gaussSum χ' ψ.char := (one_mul _).symm

end CubicFirstMoment.ReciprocityKernel

namespace CubicFirstMoment

lemma omegaE_primitive : IsPrimitiveRoot omegaE 3 :=
  IsPrimitiveRoot.of_map_of_injective (f := eisensteinRing.subtype) omega_primitive
    Subtype.val_injective

lemma cubeRoot_reduce_inj {r z w : Eisenstein} (hr : primaryPrime r)
    (hz : z^3 = 1) (hw : w^3 = 1)
    (he : Ideal.Quotient.mk (modulus r) z = Ideal.Quotient.mk (modulus r) w) : z = w := by
  obtain ⟨i,hi,hiz⟩ := omegaE_primitive.eq_pow_of_pow_eq_one hz
  obtain ⟨j,hj,hjw⟩ := omegaE_primitive.eq_pow_of_pow_eq_one hw
  rw [← hiz, ← hjw, map_pow, map_pow] at he
  have hij := (residue_omega_primitive hr).pow_inj hi hj he
  rw [← hiz, ← hjw, hij]

lemma cubicResidueCharE_cube {p : Eisenstein} (hp : primaryPrime p) :
    cubicResidueCharE p hp ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply u.isUnit]
  apply Subtype.ext
  change (cubicResidueChar p hp u)^3 = 1
  rw [← MulChar.pow_apply' _ (by norm_num), cubicResidueChar_cube hp,
    MulChar.one_apply u.isUnit]

lemma cubicResidueCharE_neg_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicResidueCharE p hp (-1) = 1 := by
  apply Subtype.ext
  change cubicResidueChar p hp (-1) = 1
  have hm : Ideal.Quotient.mk (modulus p) (-1) = (-1 : Residues p) := by
    rw [map_neg, map_one]
  rw [← hm, cubicResidueChar_mk, cubicSymbolAtPrime_neg_one hp]

lemma cubicResidueCharE_value_cube {p : Eisenstein} (hp : primaryPrime p)
    {x : Residues p} (hx : cubicResidueCharE p hp x ≠ 0) :
    (cubicResidueCharE p hp x)^3 = 1 := by
  have hu : IsUnit x := by
    by_contra hn
    exact hx ((cubicResidueCharE p hp).map_nonunit hn)
  rw [← MulChar.pow_apply' _ (by norm_num), cubicResidueCharE_cube hp,
    MulChar.one_apply hu]

lemma cubicResidueCharE_ringHomComp_ne_one {p r : Eisenstein}
    (hp : primaryPrime p) (hr : primaryPrime r) :
    (cubicResidueCharE p hp).ringHomComp (Ideal.Quotient.mk (modulus r)) ≠ 1 := by
  intro he
  apply cubicResidueChar_ne_one hp
  apply MulChar.ext
  intro u
  have hx : (cubicResidueCharE p hp u)^3 = 1 := by
    rw [← MulChar.pow_apply' _ (by norm_num), cubicResidueCharE_cube hp,
      MulChar.one_apply u.isUnit]
  have hq := congrArg (fun χ : MulChar (Residues p) (Residues r) => χ u) he
  rw [MulChar.ringHomComp_apply, MulChar.one_apply u.isUnit] at hq
  have hval := cubeRoot_reduce_inj hr hx (one_pow 3) (hq.trans (map_one _).symm)
  rw [MulChar.one_apply u.isUnit]
  exact congrArg (fun z : Eisenstein => (z : ℂ)) hval

lemma primeJacobi_eq_sumE {p : Eisenstein} (hp : primaryPrime p) [Fintype (Residues p)] :
    primeJacobi p hp = jacobiSum (cubicResidueCharE p hp) (cubicResidueCharE p hp) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  have hi : Fintype.ofFinite (Residues p) = ‹Fintype (Residues p)› := Subsingleton.elim _ _
  unfold primeJacobi
  rw [hi]

lemma normNat_cast_eq_mul_conjugate (p : Eisenstein) :
    (normNat p : Eisenstein) = p * conjugate p := by
  apply Subtype.ext
  change (normNat p : ℂ) = (p : ℂ) * (starRingEnd ℂ) (p : ℂ)
  rw [Complex.mul_conj]
  exact_mod_cast normNat_cast p

lemma cubic_reciprocity_frobenius {p r : Eisenstein} (hp : primaryPrime p)
    (hr : primaryPrime r) (hdiff : ringChar (Residues r) ≠ ringChar (Residues p)) :
    cubicSymbolAtPrime r p ^ 2 * cubicSymbolAtPrime r (conjugate p) *
      cubicSymbolAtPrime p r * cubicSymbolAtPrime p (conjugate r) = 1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : (modulus r).IsPrime := (Ideal.span_singleton_prime hr.2.ne_zero).mpr hr.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Finite (Residues r) := finite_residues hr.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Fintype (Residues r) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let : Field (Residues r) := Fintype.fieldOfDomain _
  let χ := (cubicResidueCharE p hp).ringHomComp (Ideal.Quotient.mk (modulus r))
  have hχ : χ^3 = 1 := by
    dsimp [χ]
    rw [MulChar.ringHomComp_pow, cubicResidueCharE_cube hp, MulChar.ringHomComp_one]
  have hminus : χ (-1) = 1 := by
    change Ideal.Quotient.mk (modulus r) (cubicResidueCharE p hp (-1)) = 1
    rw [cubicResidueCharE_neg_one hp, map_one]
  have hcardp : Fintype.card (Residues p) = normNat p := by
    rw [← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero]
  have hcardr : Fintype.card (Residues r) = normNat r := by
    rw [← Nat.card_eq_fintype_card, residues_card hr.2.ne_zero]
  have hthree : 3 ∣ Fintype.card (Residues r) - 1 := by
    rw [hcardr]
    exact primaryPrime_norm_sub_one_dvd_three hr
  have hJ : jacobiSum χ χ = Ideal.Quotient.mk (modulus r) (-p) := by
    dsimp [χ]
    rw [jacobiSum_ringHomComp, ← primeJacobi_eq_sumE hp, primeJacobi_eq_neg hp]
  have hrel := ReciprocityKernel.cubic_jacobi_card_relation χ hχ
    (cubicResidueCharE_ringHomComp_ne_one hp hr) hminus hthree hdiff
  rw [hJ, hcardp, hcardr] at hrel
  let z := cubicResidueCharE r hr (Ideal.Quotient.mk (modulus r) ((normNat p : Eisenstein)*(-p)))
  let w := cubicResidueCharE p hp (Ideal.Quotient.mk (modulus p) (normNat r : Eisenstein))
  have hred : Ideal.Quotient.mk (modulus r) (z*w) = 1 := by
    rw [map_mul]
    change Ideal.Quotient.mk (modulus r) (cubicResidueCharE r hr _) *
      Ideal.Quotient.mk (modulus r) w = 1
    rw [cubicResidueCharE_euler hr, map_mul, map_natCast]
    exact hrel
  have hzw : z*w ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hred
    exact zero_ne_one hred
  have hz : z^3 = 1 := cubicResidueCharE_value_cube hr (mul_ne_zero_iff.mp hzw).1
  have hw : w^3 = 1 := cubicResidueCharE_value_cube hp (mul_ne_zero_iff.mp hzw).2
  have hmul : z*w = 1 := cubeRoot_reduce_inj hr (by rw [mul_pow, hz, hw, one_mul])
    (one_pow 3) (hred.trans (map_one _).symm)
  have hc := congrArg (fun v : Eisenstein => (v : ℂ)) hmul
  simp only [z, w, Subalgebra.coe_mul, Subalgebra.coe_one,
    cubicResidueCharE_coe, cubicResidueChar_mk] at hc
  rw [normNat_cast_eq_mul_conjugate, normNat_cast_eq_mul_conjugate,
    cubicSymbolAtPrime_mul hr, cubicSymbolAtPrime_mul hr,
    cubicSymbolAtPrime_neg hr, cubicSymbolAtPrime_mul hp] at hc
  calc
    _ = (cubicSymbolAtPrime r p * cubicSymbolAtPrime r (conjugate p) *
        cubicSymbolAtPrime r p) * (cubicSymbolAtPrime p r * cubicSymbolAtPrime p (conjugate r)) := by ring
    _ = 1 := hc

theorem cubic_reciprocity_distinct_char {p r : Eisenstein} (hp : primaryPrime p)
    (hr : primaryPrime r) (hdiff : ringChar (Residues r) ≠ ringChar (Residues p)) :
    cubicSymbolAtPrime r p = cubicSymbolAtPrime p r := by
  have hpr := cubic_reciprocity_frobenius hp hr hdiff
  have hrp := cubic_reciprocity_frobenius hr hp hdiff.symm
  calc
    cubicSymbolAtPrime r p = cubicSymbolAtPrime r p * 1 := (mul_one _).symm
    _ = cubicSymbolAtPrime r p * (cubicSymbolAtPrime p r ^ 2 *
        cubicSymbolAtPrime p (conjugate r) * cubicSymbolAtPrime r p *
          cubicSymbolAtPrime r (conjugate p)) := by rw [hrp]
    _ = cubicSymbolAtPrime p r * (cubicSymbolAtPrime r p ^ 2 *
        cubicSymbolAtPrime r (conjugate p) * cubicSymbolAtPrime p r *
          cubicSymbolAtPrime p (conjugate r)) := by ring
    _ = cubicSymbolAtPrime p r := by rw [hpr, mul_one]

end CubicFirstMoment
end
end
end

end OAI
