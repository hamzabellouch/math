import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Data.Nat.Prime.Int

namespace OAI

universe uA

/-!
# Reflecting prime-power divisibility from the localized integers

A denominator inverted in the localization at `(p)` is not divisible by `p`.
Clearing that denominator and using primality therefore reflects divisibility
by every power of `p` back to the integers. The argument includes the zeroth
power and the zero numerator, without any nonzero numerator hypothesis.
-/

namespace CirculantHadamard

/-- Divisibility by a rational prime power in its actual integer localization
implies the same divisibility in the integers. -/
theorem integer_prime_pow_dvd_of_localization
    {A : Type uA} [CommRing A] [Algebra ℤ A]
    {P : Ideal ℤ} [P.IsPrime] [IsLocalization.AtPrime A P]
    {p : ℕ} (hp : p.Prime) (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ))
    (t : ℕ) (x : ℤ) (hx : (p : A) ^ t ∣ algebraMap ℤ A x) :
    (p : ℤ) ^ t ∣ x := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj P.primeCompl y
  have hinj : Function.Injective (algebraMap ℤ A) :=
    IsLocalization.injective A P.primeCompl_le_nonZeroDivisors
  have hclear : x * (s : ℤ) = (p : ℤ) ^ t * a := by
    apply hinj
    rw [map_mul, map_mul, map_pow, map_natCast, hy, mul_assoc, hs]
  have hsprime : ¬ (p : ℤ) ∣ (s : ℤ) := by
    intro hdiv
    have hmem : (s : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
      Ideal.mem_span_singleton.mpr hdiv
    exact s.property (hP.symm ▸ hmem)
  exact (Nat.prime_iff_prime_int.mp hp).pow_dvd_of_dvd_mul_right t hsprime
    ⟨a, hclear⟩

/-- Prime-power divisibility of integer coefficients is unchanged by
localization at that prime. -/
theorem integer_prime_pow_dvd_localization_iff
    {A : Type uA} [CommRing A] [Algebra ℤ A]
    {P : Ideal ℤ} [P.IsPrime] [IsLocalization.AtPrime A P]
    {p : ℕ} (hp : p.Prime) (hP : P = Ideal.span ({(p : ℤ)} : Set ℤ))
    (t : ℕ) (x : ℤ) :
    (p : A) ^ t ∣ algebraMap ℤ A x ↔ (p : ℤ) ^ t ∣ x := by
  constructor
  · exact integer_prime_pow_dvd_of_localization hp hP t x
  · intro hx
    simpa only [map_pow, map_natCast] using map_dvd (algebraMap ℤ A) hx

end CirculantHadamard

end OAI
