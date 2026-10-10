import Mathlib
import OAI.NumberTheory.CubicGram.ResidueCharacters

namespace OAI

/-! Multiplicative and additive characters and normalized prime Gauss sums. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
lemma cube_pow_mod {M : Type*} [Monoid M] {x : M} (hx : x^3 = 1) (n : ℕ) :
    x ^ (n % 3) = x ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

lemma cubicSymbol_euler_value {p v : Eisenstein} (hp : primaryPrime p)
    (hv : IsUnit (Ideal.Quotient.mk (modulus p) v)) (j : Fin 3)
    (hj : Ideal.Quotient.mk (modulus p) (v ^ ((normNat p - 1) / 3)) =
      Ideal.Quotient.mk (modulus p) (omegaE ^ (j : ℕ))) :
    cubicSymbolAtPrime p v = omega ^ (j : ℕ) := by
  have he := (cubicSymbol_euler_exists_unique hp hv).exists
  rw [cubicSymbolAtPrime, ite_eq_left hv, dite_eq_left he]
  have hh := (cubicSymbol_euler_exists_unique hp hv).unique (Classical.choose_spec he) hj
  exact congrArg (fun k : Fin 3 => omega ^ (k : ℕ)) hh

lemma cubicSymbolAtPrime_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicSymbolAtPrime p 1 = 1 := by
  have he : Ideal.Quotient.mk (modulus p) ((1 : Eisenstein) ^ ((normNat p - 1) / 3)) =
      Ideal.Quotient.mk (modulus p) (omegaE ^ (0 : ℕ)) := by simp
  simpa using cubicSymbol_euler_value hp (by simp) 0 he

lemma cubicSymbolAtPrime_mul {p : Eisenstein} (hp : primaryPrime p) (v w : Eisenstein) :
    cubicSymbolAtPrime p (v*w) = cubicSymbolAtPrime p v * cubicSymbolAtPrime p w := by
  by_cases hv : IsUnit (Ideal.Quotient.mk (modulus p) v)
  · by_cases hw : IsUnit (Ideal.Quotient.mk (modulus p) w)
    · obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
      obtain ⟨k,hk,_⟩ := cubicSymbol_euler_exists_unique hp hw
      have hjv := cubicSymbol_euler_value hp hv j hj
      have hkw := cubicSymbol_euler_value hp hw k hk
      let ℓ : Fin 3 := ⟨((j : ℕ) + (k : ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩
      have hω : (Ideal.Quotient.mk (modulus p) omegaE) ^ 3 = 1 := by
        rw [← map_pow, omegaE_cube, map_one]
      have he : Ideal.Quotient.mk (modulus p) ((v*w) ^ ((normNat p - 1) / 3)) =
          Ideal.Quotient.mk (modulus p) (omegaE ^ (ℓ : ℕ)) := by
        simp only [map_pow] at hj hk ⊢
        rw [map_mul, mul_pow, hj, hk, ← pow_add]
        exact (cube_pow_mod hω _).symm
      have hvw : IsUnit (Ideal.Quotient.mk (modulus p) (v*w)) := by
        rw [map_mul]
        exact hv.mul hw
      rw [cubicSymbol_euler_value hp hvw ℓ he, hjv, hkw, ← pow_add]
      exact cube_pow_mod omega_cube _
    · have hvw : ¬ IsUnit (Ideal.Quotient.mk (modulus p) (v*w)) := by
        rw [map_mul, (Commute.all _ _).isUnit_mul_iff]
        tauto
      simp only [cubicSymbolAtPrime, hvw, hw, ite_false, mul_zero]
  · have hvw : ¬ IsUnit (Ideal.Quotient.mk (modulus p) (v*w)) := by
      rw [map_mul, (Commute.all _ _).isUnit_mul_iff]
      tauto
    simp only [cubicSymbolAtPrime, hvw, hv, ite_false, zero_mul]

def cubicResidueChar (p : Eisenstein) (hp : primaryPrime p) : MulChar (Residues p) ℂ where
  toFun x := cubicSymbolAtPrime p (residueRepresentative p x)
  map_one' := by
    rw [cubicSymbolAtPrime_congr (show
      Ideal.Quotient.mk (modulus p) (residueRepresentative p 1) =
        Ideal.Quotient.mk (modulus p) 1 by rw [residueRepresentative_spec, map_one])]
    exact cubicSymbolAtPrime_one hp
  map_mul' x y := by
    rw [cubicSymbolAtPrime_congr (show
      Ideal.Quotient.mk (modulus p) (residueRepresentative p (x*y)) =
        Ideal.Quotient.mk (modulus p) (residueRepresentative p x * residueRepresentative p y) by
          rw [map_mul, residueRepresentative_spec, residueRepresentative_spec,
            residueRepresentative_spec])]
    exact cubicSymbolAtPrime_mul hp _ _
  map_nonunit' x hx := by
    simp only [cubicSymbolAtPrime, residueRepresentative_spec, hx, ite_false]

@[simp] lemma cubicResidueChar_mk (p : Eisenstein) (hp : primaryPrime p) (v : Eisenstein) :
    cubicResidueChar p hp (Ideal.Quotient.mk (modulus p) v) = cubicSymbolAtPrime p v :=
  cubicSymbolAtPrime_congr (residueRepresentative_spec _ _)

lemma additivePhase_add (p v w : Eisenstein) :
    additivePhase p (v+w) = additivePhase p v * additivePhase p w := by
  unfold additivePhase
  dsimp only
  simp only [Subalgebra.coe_add, add_div, star_add]
  rw [show 2 * (Real.pi : ℂ) * Complex.I *
      ((v : ℂ)/(p : ℂ) + (w : ℂ)/(p : ℂ) +
        (star ((v : ℂ)/(p : ℂ)) + star ((w : ℂ)/(p : ℂ)))) =
      2 * (Real.pi : ℂ) * Complex.I * ((v : ℂ)/(p : ℂ) + star ((v : ℂ)/(p : ℂ))) +
      2 * (Real.pi : ℂ) * Complex.I * ((w : ℂ)/(p : ℂ) + star ((w : ℂ)/(p : ℂ))) by ring,
    Complex.exp_add]

@[simp] lemma additivePhase_zero (p : Eisenstein) : additivePhase p 0 = 1 := by
  simp [additivePhase]

def residueAddChar (p : Eisenstein) (hp : p ≠ 0) : AddChar (Residues p) ℂ where
  toFun x := additivePhase p (residueRepresentative p x)
  map_zero_eq_one' := by
    rw [additivePhase_congr hp (show
      Ideal.Quotient.mk (modulus p) (residueRepresentative p 0) =
        Ideal.Quotient.mk (modulus p) 0 by rw [residueRepresentative_spec, map_zero])]
    exact additivePhase_zero p
  map_add_eq_mul' x y := by
    rw [additivePhase_congr hp (show
      Ideal.Quotient.mk (modulus p) (residueRepresentative p (x+y)) =
        Ideal.Quotient.mk (modulus p) (residueRepresentative p x + residueRepresentative p y) by
          rw [map_add, residueRepresentative_spec, residueRepresentative_spec,
            residueRepresentative_spec])]
    exact additivePhase_add _ _ _

@[simp] lemma residueAddChar_mk (p : Eisenstein) (hp : p ≠ 0) (v : Eisenstein) :
    residueAddChar p hp (Ideal.Quotient.mk (modulus p) v) = additivePhase p v :=
  additivePhase_congr hp (residueRepresentative_spec _ _)

lemma gaussAtPrime_eq_gaussSum {p : Eisenstein} (hp : primaryPrime p) [Fintype (Residues p)] :
    gaussAtPrime p = (Real.sqrt (norm p) : ℂ)⁻¹ *
      gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero) := by
  simp only [gaussAtPrime, gaussSum, tsum_fintype]
  rfl

lemma omega_primitive : IsPrimitiveRoot omega 3 := by
  apply isPrimitiveRoot_of_mem_nthRootsFinset (by norm_num : Nat.Prime 3)
  · rw [Polynomial.mem_nthRootsFinset (by norm_num : 0 < 3)]
    exact omega_cube
  · intro h
    have hh := congrArg Complex.re h
    simp only [omega_re, Complex.one_re] at hh
    norm_num at hh

lemma cubicResidueChar_ne_one {p : Eisenstein} (hp : primaryPrime p) :
    cubicResidueChar p hp ≠ 1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  intro htriv
  have hpow (u : (Residues p)ˣ) : u ^ ((normNat p - 1) / 3) = 1 := by
    let v := residueRepresentative p (u : Residues p)
    have hv : IsUnit (Ideal.Quotient.mk (modulus p) v) := by
      rw [show Ideal.Quotient.mk (modulus p) v = u from residueRepresentative_spec _ _]
      exact u.isUnit
    obtain ⟨j,hj,_⟩ := cubicSymbol_euler_exists_unique hp hv
    have hc : omega ^ (j : ℕ) = 1 := by
      rw [← cubicSymbol_euler_value hp hv j hj]
      change cubicResidueChar p hp u = 1
      rw [htriv, MulChar.one_apply u.isUnit]
    have hj0 : (j : ℕ) = 0 := omega_primitive.pow_inj j.isLt (by norm_num) (by simpa using hc)
    apply Units.ext
    simpa [map_pow, v, residueRepresentative_spec, hj0] using hj
  obtain ⟨u,hu⟩ := IsCyclic.exists_generator (α := (Residues p)ˣ)
  have horder := orderOf_eq_card_of_forall_mem_zpowers hu
  rw [Nat.card_units, residues_card hp.2.ne_zero] at horder
  have hdvd := orderOf_dvd_of_pow_eq_one (hpow u)
  rw [horder] at hdvd
  have hq : 1 < normNat p := by
    rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hpos : 0 < (normNat p - 1) / 3 := by
    exact Nat.div_pos (Nat.le_of_dvd (by omega) (primaryPrime_norm_sub_one_dvd_three hp))
      (by norm_num)
  have hle := Nat.le_of_dvd hpos hdvd
  have hlt : (normNat p - 1) / 3 < normNat p - 1 :=
    Nat.div_lt_self (by omega) (by norm_num)
  omega

lemma omega_star : star omega = -1 - omega := by
  apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]
  norm_num

lemma trace_pair_lattice {z : ℂ} {n k : ℤ}
    (h₁ : z + star z = n) (h₂ : omega*z + star (omega*z) = k) :
    3*z = ((n-k : ℤ) : ℂ) + ((-n-2*k : ℤ) : ℂ)*omega := by
  push_cast
  rw [star_mul, omega_star] at h₂
  linear_combination (1-omega)*h₁ - (1+2*omega)*h₂ + 2*(z-star z)*omega_quadratic

lemma additivePhase_eq_one_iff {p v : Eisenstein} :
    additivePhase p v = 1 ↔ ∃ n : ℤ,
      (v : ℂ)/(p : ℂ) + star ((v : ℂ)/(p : ℂ)) = n := by
  unfold additivePhase
  dsimp only
  rw [Complex.exp_eq_one_iff]
  apply exists_congr
  intro n
  rw [mul_comm (n : ℂ)]
  constructor
  · exact mul_left_cancel₀ Complex.two_pi_I_ne_zero
  · intro h
    rw [h]

lemma residueAddChar_ne_one {p : Eisenstein} (hp : primaryPrime p) :
    residueAddChar p hp.2.ne_zero ≠ 1 := by
  intro htriv
  have hall (v : Eisenstein) : additivePhase p v = 1 := by
    rw [← residueAddChar_mk p hp.2.ne_zero, htriv, AddChar.one_apply]
  obtain ⟨n,hn⟩ := additivePhase_eq_one_iff.mp (hall 1)
  obtain ⟨k,hk⟩ := additivePhase_eq_one_iff.mp (hall omegaE)
  simp only [Subalgebra.coe_one, omegaE] at hn hk
  have ht := trace_pair_lattice hn (show omega * ((1 : ℂ)/(p : ℂ)) +
      star (omega * ((1 : ℂ)/(p : ℂ))) = k by simpa [div_eq_mul_inv] using hk)
  apply primaryPrime_not_dvd_three hp
  refine ⟨ofCoords (n-k) (-n-2*k), ?_⟩
  apply Subtype.ext
  change (3 : ℂ) = (p : ℂ) * (ofCoords (n-k) (-n-2*k) : ℂ)
  rw [ofCoords_coe, ← ht]
  have hp' : (p : ℂ) ≠ 0 := fun h => hp.2.ne_zero (Subtype.ext h)
  field_simp

lemma norm_gaussAtPrime {p : Eisenstein} (hp : primaryPrime p) :
    ‖gaussAtPrime p‖ = 1 := by
  let : (modulus p).IsPrime := (Ideal.span_singleton_prime hp.2.ne_zero).mpr hp.2
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Field (Residues p) := Fintype.fieldOfDomain _
  let g := gaussSum (cubicResidueChar p hp) (residueAddChar p hp.2.ne_zero)
  have hprod := gaussSum_mul_gaussSum_eq_card (cubicResidueChar_ne_one hp)
    (AddChar.IsPrimitive.of_ne_one (residueAddChar_ne_one hp))
  rw [← star_gaussSum_eq] at hprod
  have hnormSq : (Complex.normSq g : ℂ) = (normNat p : ℂ) := by
    rw [← Complex.mul_conj]
    change g * star g = _
    rw [← residues_card hp.2.ne_zero, Nat.card_eq_fintype_card]
    exact hprod
  have hnormSq' : Complex.normSq g = norm p := by
    have hreal := congrArg Complex.re hnormSq
    simpa [normNat_cast] using hreal
  have hnorm : ‖g‖ = Real.sqrt (norm p) := by
    rw [Complex.norm_def, hnormSq']
  have hp' : (p : ℂ) ≠ 0 := fun h => hp.2.ne_zero (Subtype.ext h)
  have hpos : 0 < norm p := Complex.normSq_pos.mpr hp'
  rw [gaussAtPrime_eq_gaussSum hp, norm_mul, norm_inv]
  change ‖(Real.sqrt (norm p) : ℂ)‖⁻¹ * ‖g‖ = 1
  rw [hnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'

end CubicFirstMoment
end
end

end OAI
