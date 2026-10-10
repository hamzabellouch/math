import Mathlib
import OAI.NumberTheory.CubicGram.GaussCharacters

namespace OAI

/-! Eisenstein conjugation, characters and Gauss-sum symmetry. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid
lemma star_omega_linear : star omega = -omega - 1 := by
  apply Complex.ext <;> simp [omega_re, omega_im]; ring

lemma star_omega : star omega = omega^2 := by
  rw [star_omega_linear]
  linear_combination -omega_quadratic

lemma star_mem_eisenstein (z : Eisenstein) : star (z : ℂ) ∈ eisensteinRing := by
  obtain ⟨a,b,h⟩ := exists_coordinates z
  have hstar : star (z : ℂ) = (ofCoords (a-b) (-b) : ℂ) := by
    rw [h]
    simp only [star_add, star_mul, star_intCast, star_omega_linear, ofCoords_coe]
    push_cast
    ring
  rw [hstar]
  exact (ofCoords (a-b) (-b)).property

def conjugate : Eisenstein ≃+* Eisenstein where
  toFun z := ⟨star (z : ℂ), star_mem_eisenstein z⟩
  invFun z := ⟨star (z : ℂ), star_mem_eisenstein z⟩
  left_inv z := Subtype.ext (star_star _)
  right_inv z := Subtype.ext (star_star _)
  map_mul' z w := Subtype.ext (by simp)
  map_add' z w := Subtype.ext (by simp)

@[simp] lemma conjugate_coe (z : Eisenstein) : (conjugate z : ℂ) = star (z : ℂ) := rfl

@[simp] lemma conjugate_conjugate (z : Eisenstein) : conjugate (conjugate z) = z :=
  Subtype.ext (star_star _)

@[simp] lemma conjugate_omegaE : conjugate omegaE = omegaE^2 := Subtype.ext star_omega

@[simp] lemma norm_conjugate (z : Eisenstein) : norm (conjugate z) = norm z :=
  Complex.normSq_conj _

@[simp] lemma normNat_conjugate (z : Eisenstein) : normNat (conjugate z) = normNat z := by
  simp only [normNat, norm_conjugate]

lemma primary_conjugate {z : Eisenstein} (hz : primary z) : primary (conjugate z) := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨conjugate w, ?_⟩
  simpa only [map_sub, map_one, map_mul, map_ofNat] using congrArg conjugate hw

lemma primaryPrime_conjugate {p : Eisenstein} (hp : primaryPrime p) :
    primaryPrime (conjugate p) :=
  ⟨primary_conjugate hp.1, (MulEquiv.prime_iff conjugate).mpr hp.2⟩

def residueConjugate (p : Eisenstein) : Residues p ≃+* Residues (conjugate p) :=
  Ideal.quotientEquiv (modulus p) (modulus (conjugate p)) conjugate (by
    simp [modulus, Ideal.map_span])

@[simp] lemma residueConjugate_mk (p v : Eisenstein) :
    residueConjugate p (Ideal.Quotient.mk (modulus p) v) =
      Ideal.Quotient.mk (modulus (conjugate p)) (conjugate v) := rfl

lemma isUnit_residue_conjugate {p v : Eisenstein} :
    IsUnit (Ideal.Quotient.mk (modulus (conjugate p)) (conjugate v)) ↔
      IsUnit (Ideal.Quotient.mk (modulus p) v) := by
  constructor
  · intro h
    change IsUnit (residueConjugate p (Ideal.Quotient.mk (modulus p) v)) at h
    have hh := h.map (residueConjugate p).symm
    rw [(residueConjugate p).symm_apply_apply] at hh
    exact hh
  · intro h
    exact h.map (residueConjugate p)

lemma cubicSymbolAtPrime_conjugate {p : Eisenstein} (hp : primaryPrime p) (v : Eisenstein) :
    cubicSymbolAtPrime (conjugate p) (conjugate v) = star (cubicSymbolAtPrime p v) := by
  by_cases hv : IsUnit (Ideal.Quotient.mk (modulus p) v)
  · have hv' := isUnit_residue_conjugate.mpr hv
    obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
    let k : Fin 3 := ⟨(2*(j:ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩
    have hk : Ideal.Quotient.mk (modulus (conjugate p))
          ((conjugate v)^((normNat (conjugate p)-1)/3)) =
        Ideal.Quotient.mk (modulus (conjugate p)) (omegaE^(k:ℕ)) := by
      have heq := congrArg (residueConjugate p) hj
      simpa only [residueConjugate_mk, map_pow, conjugate_omegaE,
        normNat_conjugate, k, cube_pow_mod omegaE_cube, pow_mul] using heq
    rw [cubicSymbol_euler_value (primaryPrime_conjugate hp) hv' k hk,
      cubicSymbol_euler_value hp hv j hj, star_pow, star_omega]
    exact (cube_pow_mod omega_cube (2*(j:ℕ))).trans (pow_mul omega 2 (j:ℕ))
  · have hv' : ¬IsUnit (Ideal.Quotient.mk (modulus (conjugate p)) (conjugate v)) :=
      mt isUnit_residue_conjugate.mp hv
    simp only [cubicSymbolAtPrime, ite_eq_right hv, ite_eq_right hv', star_zero]

lemma cubicSymbolAtPrime_unit_cube {p v : Eisenstein} (hp : primaryPrime p)
    (hv : IsUnit (Ideal.Quotient.mk (modulus p) v)) :
    cubicSymbolAtPrime p v ^ 3 = 1 := by
  obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
  rw [cubicSymbol_euler_value hp hv j hj, ← pow_mul, Nat.mul_comm, pow_mul,
    omega_cube, one_pow]

lemma cubicSymbolAtPrime_neg_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbolAtPrime p (-1) = 1 := by
  have h2 : cubicSymbolAtPrime p (-1) ^ 2 = 1 := by
    rw [pow_two, ← cubicSymbolAtPrime_mul hp, neg_mul_neg, one_mul,
      cubicSymbolAtPrime_one hp]
  have h3 := cubicSymbolAtPrime_unit_cube hp
    (show IsUnit (Ideal.Quotient.mk (modulus p) (-1)) from by
      simpa only [map_neg, map_one] using (isUnit_one : IsUnit (1 : Residues p)).neg)
  rw [pow_succ, h2, one_mul] at h3
  exact h3

lemma cubicSymbolAtPrime_neg {p : Eisenstein} (hp : primaryPrime p) (v : Eisenstein) :
    cubicSymbolAtPrime p (-v) = cubicSymbolAtPrime p v := by
  rw [← neg_one_mul v, cubicSymbolAtPrime_mul hp, cubicSymbolAtPrime_neg_one hp,
    one_mul]

lemma additivePhase_conjugate (p v : Eisenstein) :
    additivePhase (conjugate p) (conjugate v) = additivePhase p v := by
  simp only [additivePhase, conjugate_coe, ← star_div₀, star_star]
  rw [add_comm (star ((v : ℂ) / (p : ℂ))) ((v : ℂ) / (p : ℂ))]

lemma additivePhase_neg {p : Eisenstein} (hp : p ≠ 0) (v : Eisenstein) :
    additivePhase p (-v) = star (additivePhase p v) := by
  let : Finite (Residues p) := finite_residues hp
  simpa only [← map_neg (Ideal.Quotient.mk (modulus p)), residueAddChar_mk, Complex.star_def] using
    (AddChar.map_neg_eq_conj (residueAddChar p hp) (Ideal.Quotient.mk (modulus p) v))

theorem gaussAtPrime_conjugate {p : Eisenstein} (hp : primaryPrime p) :
    gaussAtPrime (conjugate p) = star (gaussAtPrime p) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Finite (Residues (conjugate p)) :=
    finite_residues (primaryPrime_conjugate hp).2.ne_zero
  let : Fintype (Residues (conjugate p)) := Fintype.ofFinite _
  let e : Residues p ≃ Residues (conjugate p) := (residueConjugate p).toEquiv
  let r : Residues (conjugate p) → Eisenstein := fun x =>
    conjugate (residueRepresentative p (e.symm x))
  have hr (x) : Ideal.Quotient.mk (modulus (conjugate p)) (r x) = x := by
    change residueConjugate p (Ideal.Quotient.mk (modulus p)
      (residueRepresentative p (e.symm x))) = x
    rw [residueRepresentative_spec]
    exact e.apply_symm_apply x
  rw [gaussAtPrime_eq_finite_sum (primaryPrime_conjugate hp).2.ne_zero r hr,
    norm_conjugate]
  rw [← e.sum_comp (fun x => cubicSymbolAtPrime (conjugate p) (r x) *
    additivePhase (conjugate p) (r x))]
  simp only [r, Equiv.symm_apply_apply, cubicSymbolAtPrime_conjugate hp,
    additivePhase_conjugate]
  rw [gaussAtPrime_eq_finite_sum hp.2.ne_zero (residueRepresentative p)
    (residueRepresentative_spec p), star_mul', star_inv₀,
    show star ((Real.sqrt (norm p) : ℝ) : ℂ) = (Real.sqrt (norm p) : ℂ) from by
      simp only [Complex.star_def, Complex.conj_ofReal], star_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg (Residues p))
    (fun x => star (cubicSymbolAtPrime p (residueRepresentative p x)) *
      additivePhase p (residueRepresentative p x))]
  apply Finset.sum_congr rfl
  intro x _
  have hrep : Ideal.Quotient.mk (modulus p) (residueRepresentative p (-x)) =
      Ideal.Quotient.mk (modulus p) (-residueRepresentative p x) := by
    rw [map_neg, residueRepresentative_spec, residueRepresentative_spec]
  simp only [Equiv.neg_apply, star_mul', cubicSymbolAtPrime_congr hrep,
    additivePhase_congr hp.2.ne_zero hrep, cubicSymbolAtPrime_neg hp,
    additivePhase_neg hp.2.ne_zero]

end CubicFirstMoment
end
end

end OAI
