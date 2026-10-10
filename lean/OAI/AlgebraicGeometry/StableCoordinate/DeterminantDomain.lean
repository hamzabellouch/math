import Mathlib

namespace OAI

/-!
# Domain properties of the two concrete auxiliary rings

The determinant equation and the quadric relation are irreducible primitive
linear polynomials in one of their variables.  This file proves their
principal ideals prime, and hence the corresponding affine coordinate rings
are domains, over every unique factorization domain.
-/

noncomputable section
namespace StableCoordinate.DeterminantDomain
open MvPolynomial

variable (k : Type*) [CommRing k] [IsDomain k] [UniqueFactorizationMonoid k]

/-- Variables are ordered `a,d,b,c,u`. -/
def determinantRelation : MvPolynomial (Fin 5) k :=
  X 0 * X 3 - X 2 * X 1 - 1

/-- Variables are ordered `x,y,z,u`. -/
def quadricRelation : MvPolynomial (Fin 4) k :=
  X 0 * X 1 - X 2 * (X 2 + 1)

omit [UniqueFactorizationMonoid k] in
theorem determinantRelation_irreducible : Irreducible (determinantRelation k) := by
  have hrel : IsRelPrime (X (0 : Fin 5) : MvPolynomial (Fin 5) k)
      (-(X 2 * X 1 + 1)) := by
    apply (X_prime.irreducible).isRelPrime_iff_not_dvd.mpr
    intro h
    have he := map_dvd (eval (fun _ : Fin 5 => (0 : k))) h
    simp at he
  have hvars : (3 : Fin 5) ∉ (-(X 2 * X 1 + 1) : MvPolynomial (Fin 5) k).vars := by
    intro hv
    rw [vars_neg] at hv
    have hs := vars_add_subset (X 2 * X 1 : MvPolynomial (Fin 5) k) 1 hv
    have hm : (3 : Fin 5) ∉ (X 2 * X 1 : MvPolynomial (Fin 5) k).vars := by
      intro h
      have h := vars_mul (X 2 : MvPolynomial (Fin 5) k) (X 1) h
      simp at h
    simp [hm] at hs
  have h := irreducible_mul_X_add (X (0 : Fin 5) : MvPolynomial (Fin 5) k)
    (-(X 2 * X 1 + 1)) 3 (X_ne_zero 0) (by simp) hvars hrel
  convert h using 1
  simp only [determinantRelation]
  ring

omit [UniqueFactorizationMonoid k] in
theorem quadricRelation_irreducible : Irreducible (quadricRelation k) := by
  have hrel : IsRelPrime (X (0 : Fin 4) : MvPolynomial (Fin 4) k)
      (-(X 2 * (X 2 + 1))) := by
    apply (X_prime.irreducible).isRelPrime_iff_not_dvd.mpr
    intro h
    have h : (X (0 : Fin 4) : MvPolynomial (Fin 4) k) ∣ X 2 * (X 2 + 1) := by
      simpa using h
    rcases X_prime.dvd_mul.mp h with h | h
    · simp [X_dvd_X] at h
    · have he := map_dvd (eval (fun _ : Fin 4 => (0 : k))) h
      simp at he
  have hvars : (1 : Fin 4) ∉ (-(X 2 * (X 2 + 1)) : MvPolynomial (Fin 4) k).vars := by
    intro hv
    rw [vars_neg] at hv
    have hm := vars_mul (X 2 : MvPolynomial (Fin 4) k) (X 2 + 1) hv
    have ha : (1 : Fin 4) ∉ (X 2 + 1 : MvPolynomial (Fin 4) k).vars := by
      intro h
      have h := vars_add_subset (X 2 : MvPolynomial (Fin 4) k) 1 h
      simp at h
    simp [ha] at hm
  simpa only [quadricRelation, sub_eq_add_neg] using
    irreducible_mul_X_add (X (0 : Fin 4) : MvPolynomial (Fin 4) k)
      (-(X 2 * (X 2 + 1))) 1 (X_ne_zero 0) (by simp) hvars hrel

/-- The actual determinant hypersurface ideal is prime. -/
theorem determinantIdeal_isPrime :
    (Ideal.span {determinantRelation k}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (determinantRelation_irreducible k).prime

/-- The actual quadric hypersurface ideal is prime. -/
theorem quadricIdeal_isPrime :
    (Ideal.span {quadricRelation k}).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (quadricRelation_irreducible k).prime

/-- Coordinate ring of the determinant hypersurface, ordered `a,d,b,c,u`. -/
abbrev DeterminantRing :=
  MvPolynomial (Fin 5) k ⧸ Ideal.span {determinantRelation k}

/-- Coordinate ring of the quadric times the `u`-line, ordered `x,y,z,u`. -/
abbrev QuadricRing :=
  MvPolynomial (Fin 4) k ⧸ Ideal.span {quadricRelation k}

instance determinantRing_isDomain : IsDomain (DeterminantRing k) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr (determinantIdeal_isPrime k)

instance quadricRing_isDomain : IsDomain (QuadricRing k) :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr (quadricIdeal_isPrime k)

end StableCoordinate.DeterminantDomain

end

end OAI
