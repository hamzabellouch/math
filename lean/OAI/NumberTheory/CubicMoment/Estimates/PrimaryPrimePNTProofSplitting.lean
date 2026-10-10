import OAI.NumberTheory.CubicGram.Reciprocity

namespace OAI

/-! Rational splitting and the literal primary Eisenstein primes. -/
noncomputable section
open scoped BigOperators
open UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_natCast (n : ℕ) : normNat (n : Eisenstein) = n ^ 2 := by
  apply Nat.cast_injective (R := ℝ)
  simp only [normNat_cast, Nat.cast_pow]
  change Complex.normSq (n : ℂ) = _
  simp [Complex.normSq_apply, pow_two]

lemma isUnit_iff_normNat_eq_one (z : Eisenstein) : IsUnit z ↔ normNat z = 1 := by
  refine ⟨normNat_of_isUnit, fun h => isUnit_of_norm_eq_one ?_⟩
  rw [← normNat_cast, h, Nat.cast_one]

lemma prime_of_normNat_prime {z : Eisenstein} (hz : (normNat z).Prime) : Prime z := by
  apply irreducible_iff_prime.mp
  refine ⟨fun hu => hz.ne_one ((isUnit_iff_normNat_eq_one z).mp hu), ?_⟩
  intro a b hab
  have he : normNat a * normNat b = normNat z := by rw [← normNat_mul, ← hab]
  rcases Nat.prime_mul_iff.mp (he.symm ▸ hz) with h | h
  · exact Or.inr ((isUnit_iff_normNat_eq_one b).mpr h.2)
  · exact Or.inl ((isUnit_iff_normNat_eq_one a).mpr h.2)

lemma primary_natCast_of_mod_one {p : ℕ} (hp : p % 3 = 1) :
    primary (p : Eisenstein) := by
  refine ⟨(p / 3 : ℕ), ?_⟩
  have h := Nat.mod_add_div p 3
  rw [hp] at h
  have h' : (1 : Eisenstein) + 3 * (p / 3 : ℕ) = p := by exact_mod_cast h
  linear_combination -h'

/-- Every primary prime lies over a rational prime, and its norm has degree at most two. -/
lemma primaryPrime_rational_below {z : Eisenstein} (hz : primaryPrime z) :
    ∃ p : ℕ, p.Prime ∧ z ∣ (p : Eisenstein) ∧
      (normNat z = p ∨ normNat z = p ^ 2) := by
  let : (modulus z).IsPrime := (Ideal.span_singleton_prime hz.2.ne_zero).mpr hz.2
  let : Finite (Residues z) := finite_residues hz.2.ne_zero
  let : Fintype (Residues z) := Fintype.ofFinite _
  let : Field (Residues z) := Fintype.fieldOfDomain _
  let p := ringChar (Residues z)
  have hp : Nat.Prime p := CharP.char_is_prime (Residues z) p
  have hd : z ∣ (p : Eisenstein) := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_natCast, CharP.cast_eq_zero]
  have hn : normNat z ∣ p ^ 2 := by
    obtain ⟨b, hb⟩ := hd
    rw [← normNat_natCast, hb, normNat_mul]
    exact dvd_mul_right _ _
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow hp).mp hn
  have hne : normNat z ≠ 1 := fun h => hz.2.not_isUnit
    ((isUnit_iff_normNat_eq_one z).mpr h)
  refine ⟨p, hp, hd, ?_⟩
  interval_cases k
  · simp at he; contradiction
  · exact Or.inl (by simpa using he)
  · exact Or.inr he

/-- If its norm is a rational prime, that prime is in the split class. -/
lemma primaryPrime_norm_prime_mod_one {z : Eisenstein} (hz : primaryPrime z)
    (hn : (normNat z).Prime) : normNat z % 3 = 1 := by
  have h := primaryPrime_norm_sub_one_dvd_three hz
  have hN : 1 ≤ normNat z := hn.one_lt.le
  omega

/-- In the split residue class the rational prime is reducible in the Eisenstein ring. -/
lemma not_prime_natCast_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ¬ Prime (p : Eisenstein) := by
  intro hprime
  let : Fact p.Prime := ⟨hp⟩
  have hp0 : (p : Eisenstein) ≠ 0 := hprime.ne_zero
  let : (modulus (p : Eisenstein)).IsPrime :=
    (Ideal.span_singleton_prime hp0).mpr hprime
  let : Finite (Residues (p : Eisenstein)) := finite_residues hp0
  let : Fintype (Residues (p : Eisenstein)) := Fintype.ofFinite _
  let : Field (Residues (p : Eisenstein)) := Fintype.fieldOfDomain _
  let q := Ideal.Quotient.mk (modulus (p : Eisenstein))
  have hpzero : (p : Residues (p : Eisenstein)) = 0 := by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (dvd_refl _))
  let : CharP (Residues (p : Eisenstein)) p :=
    (CharP.charP_iff_prime_eq_zero hp).mpr hpzero
  have homega : (q omegaE) ^ p = q omegaE := by
    rw [← map_pow]
    have hpow := (cube_pow_mod omegaE_cube p).symm
    simpa only [hmod, pow_one] using congrArg q hpow
  have hfix (x : Residues (p : Eisenstein)) : x ^ p = x := by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨⟨a,b⟩, rfl⟩ := ofCoords_surjective z
    change (frobenius _ p) (q (ofCoords a b)) = q (ofCoords a b)
    simp only [ofCoords, map_add, map_mul, map_intCast]
    change (a : _) + b * (q omegaE) ^ p = _
    rw [homega]
  have hcard : Fintype.card (Residues (p : Eisenstein)) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card, residues_card hp0, normNat_natCast]
  have hdiv : Fintype.card (Residues (p : Eisenstein)) - 1 ∣ p - 1 := by
    apply (FiniteField.forall_pow_eq_one_iff (Residues (p : Eisenstein)) (p - 1)).mp
    intro u
    apply Units.ext
    have h := hfix (u : Residues (p : Eisenstein))
    have hh : (u : Residues (p : Eisenstein)) ^ (p - 1) * u = 1 * u := by
      calc
        _ = (u : Residues (p : Eisenstein)) ^ p := by
          rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
        _ = u := h
        _ = 1 * u := by simp
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      mul_right_cancel₀ u.ne_zero hh
  rw [hcard] at hdiv
  have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hdiv
  have hpsq : 1 ≤ p ^ 2 := by nlinarith [hp.two_le]
  have hle' : p ^ 2 ≤ p := by omega
  nlinarith [hp.two_le]

/-- Each split rational prime is the norm of an actual primary prime. -/
theorem exists_primaryPrime_norm_of_mod_one {p : ℕ} (hp : p.Prime)
    (hmod : p % 3 = 1) : ∃ z : Eisenstein, primaryPrime z ∧ normNat z = p := by
  have hnu : ¬ IsUnit (p : Eisenstein) := by
    rw [isUnit_iff_normNat_eq_one, normNat_natCast]
    nlinarith [hp.two_le]
  have hnpr : ¬ Irreducible (p : Eisenstein) :=
    fun h => not_prime_natCast_of_mod_one hp hmod h.prime
  have hfac : ∃ a b : Eisenstein, (p : Eisenstein) = a * b ∧
      ¬ IsUnit a ∧ ¬ IsUnit b := by
    simpa only [irreducible_iff, hnu, not_false_eq_true, true_and,
      not_forall, not_or, exists_prop] using hnpr
  obtain ⟨a,b,hab,ha,hb⟩ := hfac
  have hNa : normNat a ≠ 1 := mt (isUnit_iff_normNat_eq_one a).mpr ha
  have hNb : normNat b ≠ 1 := mt (isUnit_iff_normNat_eq_one b).mpr hb
  have hnorm : normNat a * normNat b = p ^ 2 := by
    rw [← normNat_mul, ← hab, normNat_natCast]
  have hNa' : normNat a = p := (hp.mul_eq_prime_sq_iff hNa hNb).mp hnorm |>.1
  have hprim := primary_natCast_of_mod_one hmod
  have haunit := unit_residue_of_dvd_primary hprim
    (show a ∣ (p : Eisenstein) from ⟨b,hab⟩)
  refine ⟨primaryNormalize a, ⟨primaryNormalize_primary haunit,
    prime_primaryNormalize (prime_of_normNat_prime (hNa' ▸ hp))⟩, ?_⟩
  rw [normNat_primaryNormalize, hNa']

end CubicFirstMoment

end

end OAI
