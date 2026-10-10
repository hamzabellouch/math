import Mathlib
import OAI.NumberTheory.CubicGram.IntegerBasis

namespace OAI

/-! Primitive cube roots, Euler residue characters and additive trace phases. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
lemma omega_cube : omega ^ 3 = 1 := by
  linear_combination (omega - 1) * omega_quadratic

lemma omegaE_quadratic : omegaE ^ 2 + omegaE + 1 = 0 := by
  apply Subtype.ext
  exact omega_quadratic

lemma omegaE_cube : omegaE ^ 3 = 1 := by
  apply Subtype.ext
  exact omega_cube

lemma omegaE_difference_product : (omegaE - 1) * (omegaE ^ 2 - 1) = 3 := by
  linear_combination (omegaE - 2) * omegaE_quadratic

lemma primaryPrime_not_dvd_three {p : Eisenstein} (hp : primaryPrime p) :
    ¬ p ∣ (3 : Eisenstein) := by
  intro h
  have hh : p ∣ p - 1 := dvd_trans h hp.1
  have h1 : p ∣ 1 := by simpa using dvd_sub (dvd_refl p) hh
  exact hp.2.not_isUnit (isUnit_of_dvd_one h1)

lemma residue_omega_primitive {p : Eisenstein} (hp : primaryPrime p) :
    IsPrimitiveRoot (Ideal.Quotient.mk (modulus p) omegaE) 3 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  apply isPrimitiveRoot_of_mem_nthRootsFinset (by norm_num : Nat.Prime 3)
  · rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 3)]
    rw [← map_pow, omegaE_cube, map_one]
  · intro heq
    have hd : p ∣ omegaE - 1 := by
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
      change Ideal.Quotient.mk (modulus p) (omegaE - 1) = 0
      rw [map_sub, map_one, heq, sub_self]
    apply primaryPrime_not_dvd_three hp
    rw [← omegaE_difference_product]
    exact dvd_mul_of_dvd_left hd _

lemma primaryPrime_norm_sub_one_dvd_three {p : Eisenstein} (hp : primaryPrime p) :
    3 ∣ normNat p - 1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have hω := residue_omega_primitive hp
  apply hω.dvd_of_pow_eq_one
  rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
  apply FiniteField.pow_card_sub_one_eq_one
  exact hω.isUnit (by norm_num : 3 ≠ 0) |>.ne_zero

lemma cubicSymbol_euler_exists_unique {p v : Eisenstein} (hp : primaryPrime p)
    (hv : IsUnit (Ideal.Quotient.mk (modulus p) v)) :
    ∃! j : Fin 3,
      Ideal.Quotient.mk (modulus p) (v ^ ((normNat p - 1) / 3)) =
        Ideal.Quotient.mk (modulus p) (omegaE ^ (j : ℕ)) := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  have heuler : (Ideal.Quotient.mk (modulus p) v ^ ((normNat p - 1) / 3)) ^ 3 = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel (primaryPrime_norm_sub_one_dvd_three hp)]
    rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one _ hv.ne_zero
  obtain ⟨j,hj,heq⟩ := (residue_omega_primitive hp).eq_pow_of_pow_eq_one heuler
  refine ⟨⟨j,hj⟩, ?_, ?_⟩
  · simpa only [map_pow] using heq.symm
  · intro k hk
    apply Fin.ext
    apply (residue_omega_primitive hp).pow_inj k.isLt hj
    simpa only [map_pow] using hk.symm.trans (by simpa only [map_pow] using heq.symm)

lemma residueRepresentative_spec (p : Eisenstein) (v : Residues p) :
    Ideal.Quotient.mk (modulus p) (residueRepresentative p v) = v :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective v)

lemma cubicSymbolAtPrime_congr {p v w : Eisenstein}
    (h : Ideal.Quotient.mk (modulus p) v = Ideal.Quotient.mk (modulus p) w) :
    cubicSymbolAtPrime p v = cubicSymbolAtPrime p w := by
  simp only [cubicSymbolAtPrime, map_pow, h]

lemma trace_ofCoords (a b : ℤ) :
    (ofCoords a b : ℂ) + star (ofCoords a b : ℂ) = (2*a-b : ℤ) := by
  apply Complex.ext
  · simp [ofCoords_coe, Complex.add_re, Complex.mul_re, omega_re]
    ring
  · simp

lemma trace_integral (z : Eisenstein) : ∃ n : ℤ, (z : ℂ) + star (z : ℂ) = n := by
  obtain ⟨⟨a,b⟩,rfl⟩ := ofCoords_surjective z
  exact ⟨2*a-b, trace_ofCoords a b⟩

lemma additivePhase_add_multiple {p : Eisenstein} (hp : p ≠ 0) (v w : Eisenstein) :
    additivePhase p (v + p*w) = additivePhase p v := by
  have hp' : (p : ℂ) ≠ 0 := fun h => hp (Subtype.ext h)
  obtain ⟨n,hn⟩ := trace_integral w
  have hdiv : ((v + p*w : Eisenstein) : ℂ) / (p : ℂ) =
      (v : ℂ) / (p : ℂ) + (w : ℂ) := by
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, add_div]
    rw [mul_div_cancel_left₀ _ hp']
  unfold additivePhase
  dsimp only
  rw [hdiv, star_add]
  have harg : 2 * (Real.pi : ℂ) * Complex.I *
      ((v : ℂ) / (p : ℂ) + (w : ℂ) +
        (star ((v : ℂ) / (p : ℂ)) + star (w : ℂ))) =
      2 * (Real.pi : ℂ) * Complex.I *
        ((v : ℂ) / (p : ℂ) + star ((v : ℂ) / (p : ℂ))) +
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [← hn]
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma additivePhase_congr {p v w : Eisenstein} (hp : p ≠ 0)
    (h : Ideal.Quotient.mk (modulus p) v = Ideal.Quotient.mk (modulus p) w) :
    additivePhase p v = additivePhase p w := by
  have hd : p ∣ v-w := by
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    change Ideal.Quotient.mk (modulus p) (v-w) = 0
    rw [map_sub, h, sub_self]
  obtain ⟨t,ht⟩ := hd
  have hv : v = w + p*t := by linear_combination ht
  rw [hv, additivePhase_add_multiple hp]

lemma gaussAtPrime_eq_finite_sum {p : Eisenstein} (hp : p ≠ 0)
    [Fintype (Residues p)] (reps : Residues p → Eisenstein)
    (hreps : ∀ x, Ideal.Quotient.mk (modulus p) (reps x) = x) :
    gaussAtPrime p = (Real.sqrt (norm p) : ℂ)⁻¹ *
      ∑ x : Residues p, cubicSymbolAtPrime p (reps x) * additivePhase p (reps x) := by
  unfold gaussAtPrime
  rw [tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hrep : Ideal.Quotient.mk (modulus p) (residueRepresentative p x) =
      Ideal.Quotient.mk (modulus p) (reps x) := by
    rw [residueRepresentative_spec, hreps]
  rw [cubicSymbolAtPrime_congr hrep, additivePhase_congr hp hrep]

end CubicFirstMoment
end
end

end OAI
