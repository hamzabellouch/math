import Mathlib
import OAI.NumberTheory.CubicGram.Conjugation
import OAI.NumberTheory.CubicGram.PrimaryNormalization

namespace OAI

/-! Cubic Jacobi sums and the prime Gauss cube identity. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
lemma cubicResidueChar_cube {p : Eisenstein} (hp : primaryPrime p) :
    cubicResidueChar p hp ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply u.isUnit]
  apply cubicSymbolAtPrime_unit_cube hp
  rw [residueRepresentative_spec]
  exact u.isUnit

lemma cubicResidueChar_order {p : Eisenstein} (hp : primaryPrime p) :
    orderOf (cubicResidueChar p hp) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (cubicResidueChar_cube hp) (cubicResidueChar_ne_one hp)

lemma cubicResidueChar_mem (p : Eisenstein) (hp : primaryPrime p) (x : Residues p) :
    cubicResidueChar p hp x ∈ eisensteinRing := by
  change cubicSymbolAtPrime p (residueRepresentative p x) ∈ eisensteinRing
  unfold cubicSymbolAtPrime
  split_ifs <;> first
  | exact eisensteinRing.zero_mem
  | exact eisensteinRing.pow_mem (Algebra.subset_adjoin (Set.mem_singleton omega)) _

def cubicResidueCharE (p : Eisenstein) (hp : primaryPrime p) :
    MulChar (Residues p) Eisenstein where
  toFun x := ⟨cubicResidueChar p hp x, cubicResidueChar_mem p hp x⟩
  map_one' := Subtype.ext (map_one (cubicResidueChar p hp))
  map_mul' x y := Subtype.ext (map_mul (cubicResidueChar p hp) x y)
  map_nonunit' _ hx := Subtype.ext ((cubicResidueChar p hp).map_nonunit hx)

@[simp] lemma cubicResidueCharE_coe (p : Eisenstein) (hp : primaryPrime p) (x : Residues p) :
    (cubicResidueCharE p hp x : ℂ) = cubicResidueChar p hp x := rfl

lemma cubicResidueCharE_euler {p : Eisenstein} (hp : primaryPrime p) (x : Residues p) :
    Ideal.Quotient.mk (modulus p) (cubicResidueCharE p hp x) =
      x ^ ((normNat p - 1) / 3) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  by_cases hx : IsUnit x
  · have hv : IsUnit (Ideal.Quotient.mk (modulus p) (residueRepresentative p x)) := by
      rwa [residueRepresentative_spec]
    obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
    have he : cubicResidueCharE p hp x = omegaE ^ (j : ℕ) := by
      apply Subtype.ext
      exact cubicSymbol_euler_value hp hv j hj
    rw [he]
    simpa only [map_pow, residueRepresentative_spec] using hj.symm
  · have hx0 : x = 0 := by simpa only [isUnit_iff_ne_zero, not_ne_iff] using hx
    have hq : 1 < normNat p := by
      rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hk : (normNat p - 1) / 3 ≠ 0 := by
      have := Nat.div_pos
        (Nat.le_of_dvd (by omega) (primaryPrime_norm_sub_one_dvd_three hp))
        (by norm_num : 0 < 3)
      omega
    rw [(cubicResidueCharE p hp).map_nonunit hx, map_zero, hx0, zero_pow hk]

def primeJacobi (p : Eisenstein) (hp : primaryPrime p) : Eisenstein :=
  letI : Finite (Residues p) := finite_residues hp.2.ne_zero
  letI : Fintype (Residues p) := Fintype.ofFinite _
  jacobiSum (cubicResidueCharE p hp) (cubicResidueCharE p hp)

lemma primeJacobi_coe {p : Eisenstein} (hp : primaryPrime p) [Fintype (Residues p)] :
    (primeJacobi p hp : ℂ) = jacobiSum (cubicResidueChar p hp) (cubicResidueChar p hp) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  have hi : Fintype.ofFinite (Residues p) = ‹Fintype (Residues p)› := Subsingleton.elim _ _
  unfold primeJacobi
  rw [hi]
  unfold jacobiSum
  change (eisensteinRing.subtype : Eisenstein →+* ℂ) (∑ x, _) = _
  rw [map_sum]
  rfl

lemma primeJacobi_primary {p : Eisenstein} (hp : primaryPrime p) :
    primary (-primeJacobi p hp) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hn : 3 ∣ Fintype.card (Residues p) - 1 := by
    rw [← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero]
    exact primaryPrime_norm_sub_one_dvd_three hp
  obtain ⟨z,hz,hJ⟩ := exists_jacobiSum_eq_neg_one_add (by norm_num : 2 < 3)
    (cubicResidueChar_cube hp) (cubicResidueChar_cube hp) hn omega_primitive
  change (3 : Eisenstein) ∣ -primeJacobi p hp - 1
  refine ⟨⟨z,hz⟩ * omegaE, ?_⟩
  apply Subtype.ext
  change -(primeJacobi p hp : ℂ) - 1 = 3 * (z * omega)
  rw [primeJacobi_coe hp, hJ]
  linear_combination -z * omega_quadratic

lemma primeJacobi_dvd {p : Eisenstein} (hp : primaryPrime p) :
    p ∣ primeJacobi p hp := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk (modulus p) (primeJacobi p hp) = 0
  unfold primeJacobi jacobiSum
  simp only [map_sum, map_mul, cubicResidueCharE_euler hp]
  let k := (normNat p - 1) / 3
  have hcard : Fintype.card (Residues p) = normNat p := by
    rw [← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero]
  have hq : 1 < normNat p := hcard ▸ Fintype.one_lt_card
  have hk : 3*k = normNat p - 1 := Nat.mul_div_cancel' (primaryPrime_norm_sub_one_dvd_three hp)
  have hkpos : 0 < k := by omega
  have hexp (x : Residues p) : x^k * (1-x)^k =
      ∑ i ∈ Finset.range (k+1), ((-1 : Residues p)^(i+k) * (k.choose i)) * x^(k+(k-i)) := by
    rw [sub_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [one_pow, mul_one, pow_add]
    ring
  change (∑ x : Residues p, x^k * (1-x)^k) = 0
  simp_rw [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
  rw [hcard]
  omega

lemma gaussAtPrime_cube_jacobi {p : Eisenstein} (hp : primaryPrime p) :
    gaussAtPrime p ^ 3 = (Real.sqrt (norm p) : ℂ)⁻¹ * (primeJacobi p hp : ℂ) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hχ := cubicResidueChar_order hp
  have hg := gaussSum_pow_eq_prod_jacobiSum (by rw [hχ]; norm_num :
      2 ≤ orderOf (cubicResidueChar p hp))
    (AddChar.IsPrimitive.of_ne_one (residueAddChar_ne_one hp))
  rw [hχ] at hg
  have hminus : cubicResidueChar p hp (-1) = 1 := by
    have hm : Ideal.Quotient.mk (modulus p) (-1) = (-1 : Residues p) := by
      rw [map_neg, map_one]
    rw [← hm, cubicResidueChar_mk, cubicSymbolAtPrime_neg_one hp]
  norm_num [hminus, Finset.prod_Ico_succ_top, ← primeJacobi_coe hp] at hg
  have hs : 0 < Real.sqrt (norm p) := Real.sqrt_pos.mpr
    (lt_of_le_of_ne (norm_nonneg p) (Ne.symm ((norm_eq_zero_iff).not.mpr hp.2.ne_zero)))
  have hs2 : (Real.sqrt (norm p) : ℂ)^2 = (norm p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (norm_nonneg p)
  have hn : (Fintype.card (Residues p) : ℂ) = (norm p : ℂ) := by
    rw [← Nat.card_eq_fintype_card, residues_card hp.2.ne_zero]
    exact_mod_cast normNat_cast p
  rw [gaussAtPrime_eq_gaussSum hp, mul_pow, hg, hn, ← hs2]
  have hs0 : (Real.sqrt (norm p) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  field_simp

lemma norm_primeJacobi {p : Eisenstein} (hp : primaryPrime p) :
    norm (primeJacobi p hp) = norm p := by
  have h := congrArg (fun z : ℂ => ‖z‖) (gaussAtPrime_cube_jacobi hp)
  rw [norm_pow, norm_gaussAtPrime hp, one_pow, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hs : 0 < Real.sqrt (norm p) := Real.sqrt_pos.mpr
    (lt_of_le_of_ne (norm_nonneg p) (Ne.symm ((norm_eq_zero_iff).not.mpr hp.2.ne_zero)))
  have hJ : ‖(primeJacobi p hp : ℂ)‖ = Real.sqrt (norm p) := by
    rw [← div_eq_inv_mul, eq_div_iff hs.ne'] at h
    simpa using h.symm
  change Complex.normSq _ = _
  rw [← Complex.sq_norm, hJ, Real.sq_sqrt (norm_nonneg p)]

lemma isUnit_of_norm_eq_one {z : Eisenstein} (hz : norm z = 1) : IsUnit z := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨conjugate z, ?_⟩
  apply Subtype.ext
  change (z : ℂ) * (starRingEnd ℂ) (z : ℂ) = 1
  rw [Complex.mul_conj]
  exact_mod_cast hz

lemma primeJacobi_eq_neg {p : Eisenstein} (hp : primaryPrime p) :
    primeJacobi p hp = -p := by
  obtain ⟨u, hu⟩ := primeJacobi_dvd hp
  have hn := norm_primeJacobi hp
  have hmul : norm (p*u) = norm p * norm u := map_mul Complex.normSq _ _
  rw [hu, hmul] at hn
  have hp0 : norm p ≠ 0 := (norm_eq_zero_iff).not.mpr hp.2.ne_zero
  have hnu : norm u = 1 := (mul_left_cancel₀ hp0 (by simpa using hn))
  have hunit := isUnit_of_norm_eq_one hnu
  have hassoc : Associated (-primeJacobi p hp) p := by
    rw [hu]
    rw [show -(p*u) = p * (-u) by ring]
    exact (associated_mul_unit_right p (-u) hunit.neg).symm
  have he := primary_associated_eq (primeJacobi_primary hp) hp.1 hassoc
  exact neg_eq_iff_eq_neg.mp he

theorem gaussAtPrime_cube {p : Eisenstein} (hp : primaryPrime p) :
    gaussAtPrime p ^ 3 = -(p : ℂ) / (Real.sqrt (norm p) : ℂ) := by
  rw [gaussAtPrime_cube_jacobi hp, primeJacobi_eq_neg hp]
  simp only [Subalgebra.coe_neg, div_eq_mul_inv]
  ring

end CubicFirstMoment

end
end

end OAI
