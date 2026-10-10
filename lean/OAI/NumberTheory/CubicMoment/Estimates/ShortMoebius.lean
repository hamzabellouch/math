import OAI.NumberTheory.CubicGram.Mobius
import Mathlib.RingTheory.MvPowerSeries.Inverse

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

abbrev EisensteinIdealPrime := {p : Associates Eisenstein // Irreducible p}
abbrev EisensteinIdealExponent := EisensteinIdealPrime →₀ ℕ
abbrev EisensteinArithmeticFunction := MvPowerSeries EisensteinIdealPrime ℝ

def idealPrimeRepresentative (p : EisensteinIdealPrime) : Eisenstein := Quotient.out p.val

lemma idealPrimeRepresentative_irreducible (p : EisensteinIdealPrime) :
    Irreducible (idealPrimeRepresentative p) := by
  apply Associates.irreducible_mk.mp
  simpa only [idealPrimeRepresentative, Associates.quotient_out] using p.property

/-- A generator of the ideal represented by its prime exponent vector. -/
def idealExponentGenerator (ν : EisensteinIdealExponent) : Eisenstein :=
  ν.prod (fun p k => idealPrimeRepresentative p ^ k)

def idealExponentNorm (ν : EisensteinIdealExponent) : ℝ :=
  (normNat (idealExponentGenerator ν) : ℝ)

lemma idealExponentGenerator_add (ν κ : EisensteinIdealExponent) :
    idealExponentGenerator (ν + κ) = idealExponentGenerator ν * idealExponentGenerator κ :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

lemma idealExponentGenerator_of_multiset (s : Multiset EisensteinIdealPrime) :
    idealExponentGenerator s.toFinsupp = (s.map idealPrimeRepresentative).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [idealExponentGenerator]
  | @cons p s ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, idealExponentGenerator_add, ih]
    simp [idealExponentGenerator]

/-- The exponent vector of every nonzero Eisenstein principal ideal. -/
def idealExponentOf (a : Eisenstein) : EisensteinIdealExponent :=
  (Associates.factors' a).toFinsupp

lemma idealExponentOf_associated {a : Eisenstein} (ha : a ≠ 0) :
    Associated (idealExponentGenerator (idealExponentOf a)) a := by
  apply Associates.mk_eq_mk_iff_associated.mp
  rw [idealExponentOf, idealExponentGenerator_of_multiset]
  have hmap : (Associates.factors' a).map
      (fun p => Associates.mk (idealPrimeRepresentative p)) =
      (Associates.factors' a).map Subtype.val := by
    apply Multiset.map_congr rfl
    intro p hp
    exact Associates.quotient_out p.val
  calc
    Associates.mk (((Associates.factors' a).map idealPrimeRepresentative).prod) =
        ((Associates.factors' a).map Subtype.val).prod := by
      change Associates.mkMonoidHom _ = _
      rw [map_multiset_prod, Multiset.map_map]
      change ((Associates.factors' a).map
        (fun p => Associates.mk (idealPrimeRepresentative p))).prod = _
      rw [hmap]
    _ = ((UniqueFactorizationMonoid.factors a).map Associates.mk).prod := by
      rw [Associates.map_subtype_coe_factors']
    _ = Associates.mk ((UniqueFactorizationMonoid.factors a).prod) := by
      exact (map_multiset_prod Associates.mkMonoidHom _).symm
    _ = Associates.mk a := Associates.mk_eq_mk_iff_associated.mpr
      (UniqueFactorizationMonoid.factors_prod ha)

lemma idealExponentOf_mul {a b : Eisenstein} (ha : a ≠ 0) (hb : b ≠ 0) :
    idealExponentOf (a * b) = idealExponentOf a + idealExponentOf b := by
  have h := Associates.factors_mul (Associates.mk a) (Associates.mk b)
  rw [Associates.mk_mul_mk, Associates.factors_mk (a * b) (mul_ne_zero ha hb),
    Associates.factors_mk a ha, Associates.factors_mk b hb] at h
  have hs : Associates.factors' (a * b) = Associates.factors' a + Associates.factors' b :=
    WithTop.coe_inj.mp h
  simp only [idealExponentOf, hs, Multiset.toFinsupp_add]

lemma idealExponentOf_norm {a : Eisenstein} (ha : a ≠ 0) :
    idealExponentNorm (idealExponentOf a) = norm a := by
  unfold idealExponentNorm
  rw [associated_normNat (idealExponentOf_associated ha), normNat_cast]

lemma idealExponentGenerator_ne_zero (ν : EisensteinIdealExponent) :
    idealExponentGenerator ν ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (idealPrimeRepresentative_irreducible p).ne_zero

lemma idealExponentNorm_ge_one (ν : EisensteinIdealExponent) : 1 ≤ idealExponentNorm ν := by
  change (1 : ℝ) ≤ (normNat (idealExponentGenerator ν) : ℝ)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (normNat_ne_zero (idealExponentGenerator_ne_zero ν))

lemma idealExponentNorm_pos (ν : EisensteinIdealExponent) : 0 < idealExponentNorm ν :=
  zero_lt_one.trans_le (idealExponentNorm_ge_one ν)

lemma idealExponentNorm_add (ν κ : EisensteinIdealExponent) :
    idealExponentNorm (ν + κ) = idealExponentNorm ν * idealExponentNorm κ := by
  simp only [idealExponentNorm, idealExponentGenerator_add, normNat_mul, Nat.cast_mul]

lemma idealExponentNorm_mono {ν κ : EisensteinIdealExponent} (h : ν ≤ κ) :
    idealExponentNorm ν ≤ idealExponentNorm κ := by
  rw [← add_tsub_cancel_of_le h, idealExponentNorm_add]
  exact le_mul_of_one_le_right (idealExponentNorm_pos ν).le (idealExponentNorm_ge_one _)

def idealZeta : EisensteinArithmeticFunction := fun _ => 1

lemma idealExponentNorm_single (p : EisensteinIdealPrime) (n : ℕ) :
    idealExponentNorm (Finsupp.single p n) =
      (normNat (idealPrimeRepresentative p) : ℝ) ^ n := by
  unfold idealExponentNorm idealExponentGenerator
  rw [Finsupp.prod_single_index (h := fun p k => idealPrimeRepresentative p ^ k) (pow_zero _)]
  have h := map_pow normNatHom (idealPrimeRepresentative p) n
  change normNat (idealPrimeRepresentative p ^ n) =
    normNat (idealPrimeRepresentative p) ^ n at h
  rw [h, Nat.cast_pow]

/-- On the powers of one prime ideal, Dirichlet convolution with the
constant-one function is the ordinary partial sum of coefficients. -/
lemma coeff_mul_zeta_single (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) =
      ∑ k ∈ Finset.range (n + 1), MvPowerSeries.coeff (Finsupp.single p k) A := by
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk,
    MvPowerSeries.coeff_apply, idealZeta, mul_one]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k _ => A (Finsupp.single p k)) n

lemma coeff_single_eq_zeta_difference (A : EisensteinArithmeticFunction)
    (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) A =
      MvPowerSeries.coeff (Finsupp.single p (n + 1)) (A * idealZeta) -
        MvPowerSeries.coeff (Finsupp.single p n) (A * idealZeta) := by
  rw [coeff_mul_zeta_single, coeff_mul_zeta_single, Finset.sum_range_succ]
  ring

/-- The ideal Möbius function, characterized as the Dirichlet inverse of
the constant-one arithmetic function. -/
def idealMoebiusSeries : EisensteinArithmeticFunction := idealZeta⁻¹

lemma idealMoebiusSeries_mul_zeta : idealMoebiusSeries * idealZeta = 1 := by
  apply MvPowerSeries.inv_mul_cancel
  change (1 : ℝ) ≠ 0
  norm_num

lemma idealZeta_mul_moebiusSeries : idealZeta * idealMoebiusSeries = 1 := by
  rw [mul_comm, idealMoebiusSeries_mul_zeta]

/-- The convolution inverse has the usual arithmetic Möbius values on
all positive powers of a prime ideal. -/
lemma idealMoebiusSeries_prime_power (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) idealMoebiusSeries =
      if n = 0 then -1 else 0 := by
  rw [coeff_single_eq_zeta_difference, idealMoebiusSeries_mul_zeta]
  simp only [MvPowerSeries.coeff_one, Finsupp.single_eq_zero]
  split_ifs <;> simp_all

def shortIdealMoebius (F : ℝ) : EisensteinArithmeticFunction :=
  fun ν => if idealExponentNorm ν ≤ Real.sqrt F then MvPowerSeries.coeff ν idealMoebiusSeries else 0

def shortMoebiusResidual (F : ℝ) : EisensteinArithmeticFunction :=
  1 - shortIdealMoebius F * idealZeta

private lemma exponent_fst_le {ν : EisensteinIdealExponent}
    {p : EisensteinIdealExponent × EisensteinIdealExponent}
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal ν) :
    p.1 ≤ ν := by
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← h]
  exact le_add_of_nonneg_right zero_le

private lemma exponent_snd_le {ν : EisensteinIdealExponent}
    {p : EisensteinIdealExponent × EisensteinIdealExponent}
    (hp : p ∈ Finset.HasAntidiagonal.antidiagonal ν) :
    p.2 ≤ ν := by
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [← h]
  exact le_add_of_nonneg_left zero_le

/-- The truncated Möbius inverse agrees with the full inverse on every
divisor of an ideal whose norm is at most the truncation threshold. -/
lemma shortMoebiusResidual_low_norm (F : ℝ) (ν : EisensteinIdealExponent)
    (hν : idealExponentNorm ν ≤ Real.sqrt F) :
    MvPowerSeries.coeff ν (shortMoebiusResidual F) = 0 := by
  have he : MvPowerSeries.coeff ν (shortIdealMoebius F * idealZeta) =
      MvPowerSeries.coeff ν (idealMoebiusSeries * idealZeta) := by
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hn := (idealExponentNorm_mono (exponent_fst_le hp)).trans hν
    simp only [MvPowerSeries.coeff_apply, shortIdealMoebius, ite_eq_left hn]
  change MvPowerSeries.coeff ν (1 - shortIdealMoebius F * idealZeta) = 0
  rw [map_sub, he, idealMoebiusSeries_mul_zeta, sub_self]

/-- Both nonzero factors of the residual must have norm greater than
`sqrt F`; hence its square vanishes throughout the actual norm ball `F`. -/
lemma shortMoebiusResidual_sq_low_norm {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν ((shortMoebiusResidual F) ^ 2) = 0 := by
  rw [pow_two, MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hfst : idealExponentNorm p.1 ≤ Real.sqrt F
  · rw [shortMoebiusResidual_low_norm F p.1 hfst, zero_mul]
  · have hsnd : idealExponentNorm p.2 ≤ Real.sqrt F := by
      have hprod : idealExponentNorm p.1 * idealExponentNorm p.2 ≤ F := by
        rw [← idealExponentNorm_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
        exact hν
      have hroot := Real.sqrt_nonneg F
      have hsq := Real.sq_sqrt hF
      by_contra h
      have ha := lt_of_not_ge hfst
      have hb := lt_of_not_ge h
      nlinarith
    rw [shortMoebiusResidual_low_norm F p.2 hsnd, mul_zero]

lemma shortMoebiusResidual_sq_mul_low_norm {F : ℝ} (hF : 0 ≤ F)
    (L : EisensteinArithmeticFunction) (ν : EisensteinIdealExponent)
    (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν ((shortMoebiusResidual F) ^ 2 * L) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [shortMoebiusResidual_sq_low_norm hF p.1
    ((idealExponentNorm_mono (exponent_fst_le hp)).trans hν), zero_mul]

def idealLogNorm : EisensteinArithmeticFunction := fun ν => Real.log (idealExponentNorm ν)

/-- The usual convolution definition of the ideal von Mangoldt function. -/
def idealVonMangoldt : EisensteinArithmeticFunction := idealMoebiusSeries * idealLogNorm

lemma idealZeta_mul_vonMangoldt : idealZeta * idealVonMangoldt = idealLogNorm := by
  rw [idealVonMangoldt, ← mul_assoc, idealZeta_mul_moebiusSeries, one_mul]

/-- The ideal von Mangoldt weight on every positive prime power is
exactly the logarithm of the prime-ideal norm. -/
lemma idealVonMangoldt_prime_power (p : EisensteinIdealPrime) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single p (n + 1)) idealVonMangoldt =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  rw [coeff_single_eq_zeta_difference, mul_comm idealVonMangoldt idealZeta,
    idealZeta_mul_vonMangoldt]
  simp only [MvPowerSeries.coeff_apply, idealLogNorm, idealExponentNorm_single,
    Real.log_pow]
  push_cast
  ring

/-- The short Möbius convolution identity throughout the sharp norm ball. -/
theorem short_moebius_identity {F : ℝ} (hF : 0 ≤ F)
    (ν : EisensteinIdealExponent) (hν : idealExponentNorm ν ≤ F) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν
        ((2 * shortIdealMoebius F - shortIdealMoebius F * shortIdealMoebius F * idealZeta) *
          idealLogNorm) := by
  have halg : idealVonMangoldt -
      (2 * shortIdealMoebius F - shortIdealMoebius F * shortIdealMoebius F * idealZeta) *
        (idealZeta * idealVonMangoldt) = (shortMoebiusResidual F) ^ 2 * idealVonMangoldt := by
    unfold shortMoebiusResidual
    ring
  have h := congrArg (MvPowerSeries.coeff ν) halg
  rw [map_sub, idealZeta_mul_vonMangoldt,
    shortMoebiusResidual_sq_mul_low_norm hF idealVonMangoldt ν hν] at h
  exact sub_eq_zero.mp h

end CubicFirstMoment

end

end OAI
