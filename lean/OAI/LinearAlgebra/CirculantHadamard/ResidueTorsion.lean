import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.GroupTheory.OrderOfElement

namespace OAI

universe uR uK

/-!
# Torsion in the kernel of a residue map

The geometric-sum argument works for any ring homomorphism from a domain
to a field of characteristic `p`. In a local-ring application the map is
the residue homomorphism; the domain itself need not have characteristic `p`.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R] [Field K]

/-- A root whose image is one is trivial if one of its torsion exponents
is not divisible by the target characteristic. -/
theorem eq_one_of_residue_one_of_not_dvd {p m : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hmap : f z = 1) (hpow : z ^ m = 1)
    (hm : ¬ p ∣ m) : z = 1 := by
  by_contra hne
  have hprod : (∑ i ∈ Finset.range m, z ^ i) * (z - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have hsum : (∑ i ∈ Finset.range m, z ^ i) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hne)
  have hcast : (m : K) = 0 := by
    have h := congrArg f hsum
    simpa only [map_sum, map_pow, hmap, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
  exact hm ((CharP.cast_eq_zero_iff K p m).mp hcast)

/-- Coprime-order torsion in the residue-one subgroup is trivial. The
exponent need not be the exact order. -/
theorem eq_one_of_residue_one_of_coprime {p m : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hpow : z ^ m = 1) (hcop : m.Coprime p) : z = 1 := by
  exact eq_one_of_residue_one_of_not_dvd f z hmap hpow
    (hp.coprime_iff_not_dvd.mp hcop.symm)

theorem exists_prime_power_of_residue_one {p : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hfinite : ∃ N : ℕ, 0 < N ∧ z ^ N = 1) :
    ∃ a : ℕ, z ^ (p ^ a) = 1 := by
  obtain ⟨N, hN, hpow⟩ := hfinite
  obtain ⟨a, m, hm, hNm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.ne_one
  refine ⟨a, eq_one_of_residue_one_of_not_dvd f (z ^ (p ^ a)) ?_ ?_ hm⟩
  · rw [map_pow, hmap, one_pow]
  · rw [← pow_mul, ← hNm]
    exact hpow

/-- The exact order is a power of the residue characteristic, including
the zeroth power for the identity element. -/
theorem orderOf_eq_prime_power_of_residue_one {p : ℕ} [CharP K p]
    (f : R →+* K) (z : R) (hp : p.Prime) (hmap : f z = 1)
    (hfinite : IsOfFinOrder z) : ∃ a : ℕ, orderOf z = p ^ a := by
  obtain ⟨a, ha⟩ := exists_prime_power_of_residue_one f z hp hmap
    hfinite.exists_pow_eq_one
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one ha)
  exact ⟨b, hb⟩

/-- The characteristic-two consequence needed for the two alternating
products: a unit of odd torsion exponent and residue one equals one. -/
theorem units_eq_one_of_residue_one_of_odd [CharP K 2]
    (f : R →+* K) (u : Rˣ) (hmap : f (u : R) = 1)
    (hfinite : ∃ m : ℕ, 0 < m ∧ Odd m ∧ u ^ m = 1) : u = 1 := by
  obtain ⟨m, _, hm, hu⟩ := hfinite
  have hpow : (u : R) ^ m = 1 := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun v : Rˣ => (v : R)) hu
  apply Units.ext
  exact eq_one_of_residue_one_of_coprime f (u : R) Nat.prime_two hmap hpow
    hm.coprime_two_right

end CirculantHadamard

end OAI
