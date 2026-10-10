import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace OAI

/-!
# The two-localization intersection used in the rigidity argument

This module supplies the denominator-clearing step in Section 5 of the source:
for relatively prime elements `a` and `d` in a unique factorization domain,
the localizations away from `a` and `d` intersect in the original ring inside
its fraction field.  Relative primeness here means that every common divisor
is a unit; it does *not* incorrectly assume that the ideal `(a,d)` is the unit
ideal.
-/

namespace StableCoordinate

section DenominatorClearing

variable {A K : Type*} [CommRing A] [IsDomain A] [DecompositionMonoid A]
  [CommRing K] [IsDomain K] [Algebra A K]

/-- Clearing two relatively prime power denominators forces an element of an
overring into the original ring.  The overring need not be a field. -/
theorem exists_algebraMap_eq_of_two_power_denominators
    (hinj : Function.Injective (algebraMap A K))
    {a d : A} (ha : a ≠ 0) (had : IsRelPrime a d)
    {z : K} {m n : ℕ} {r s : A}
    (hr : z * algebraMap A K (a ^ m) = algebraMap A K r)
    (hs : z * algebraMap A K (d ^ n) = algebraMap A K s) :
    ∃ t : A, algebraMap A K t = z := by
  have hcross : r * d ^ n = s * a ^ m := by
    apply hinj
    simp only [map_mul]
    rw [← hr, ← hs]
    exact mul_right_comm _ _ _
  have hdiv : a ^ m ∣ r :=
    had.pow.dvd_of_dvd_mul_right (hcross ▸ dvd_mul_left (a ^ m) s)
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨t, ?_⟩
  apply mul_right_cancel₀ (show algebraMap A K (a ^ m) ≠ 0 from
    fun h ↦ pow_ne_zero m ha (hinj (h.trans (map_zero _).symm)))
  rw [hr, ht, map_mul, mul_comm]

end DenominatorClearing

section FractionField

variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- Powers of a nonzero element are legitimate fraction-field denominators. -/
theorem powers_le_nonZeroDivisors {a : A} (ha : a ≠ 0) :
    Submonoid.powers a ≤ nonZeroDivisors A := by
  rintro s ⟨n, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n ha)

/-- The localization `A[a⁻¹]`, realized as an actual subalgebra of a fraction field. -/
noncomputable def awayInFractionField (a : A) (ha : a ≠ 0) : Subalgebra A K :=
  Localization.subalgebra.ofField K (Submonoid.powers a) (powers_le_nonZeroDivisors ha)

/-- Membership in a one-element localization can be expressed by clearing a
power denominator. -/
theorem mem_awayInFractionField_iff (a : A) (ha : a ≠ 0) (z : K) :
    z ∈ awayInFractionField K a ha ↔
      ∃ (n : ℕ) (r : A), z * algebraMap A K (a ^ n) = algebraMap A K r := by
  change (∃ (r s : A) (_ : s ∈ Submonoid.powers a),
    z = algebraMap A K r * (algebraMap A K s)⁻¹) ↔ _
  constructor
  · rintro ⟨r, s, ⟨n, rfl⟩, hz⟩
    refine ⟨n, r, ?_⟩
    have hnonzero : algebraMap A K (a ^ n) ≠ 0 :=
      fun h ↦ pow_ne_zero n ha (IsFractionRing.injective A K (h.trans (map_zero _).symm))
    exact (eq_div_iff hnonzero).mp (by simpa only [div_eq_mul_inv] using hz)
  · rintro ⟨n, r, hz⟩
    refine ⟨r, a ^ n, ⟨n, rfl⟩, ?_⟩
    have hnonzero : algebraMap A K (a ^ n) ≠ 0 :=
      fun h ↦ pow_ne_zero n ha (IsFractionRing.injective A K (h.trans (map_zero _).symm))
    simpa only [div_eq_mul_inv] using (eq_div_iff hnonzero).mpr hz

variable [DecompositionMonoid A]

/-- The two principal localizations at relatively prime elements intersect
in the base ring, as subalgebras of its fraction field. -/
theorem awayInFractionField_inf_eq_bot {a d : A} (ha : a ≠ 0) (hd : d ≠ 0)
    (had : IsRelPrime a d) :
    awayInFractionField K a ha ⊓ awayInFractionField K d hd = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨m, r, hr⟩ := (mem_awayInFractionField_iff K a ha z).mp hz.1
  obtain ⟨n, s, hs⟩ := (mem_awayInFractionField_iff K d hd z).mp hz.2
  exact Algebra.mem_bot.mpr
    (exists_algebraMap_eq_of_two_power_denominators
      (IsFractionRing.injective A K) ha had hr hs)

end FractionField

section PolynomialVariables

variable {k σ : Type*} [Field k]

/-- Distinct independent polynomial variables are relatively prime in the
common-divisor sense required by the intersection argument. -/
theorem isRelPrime_X_of_ne {i j : σ} (hij : i ≠ j) :
    IsRelPrime (MvPolynomial.X i : MvPolynomial σ k) (MvPolynomial.X j) := by
  apply MvPolynomial.X_prime.irreducible.isRelPrime_iff_not_dvd.mpr
  simpa only [MvPolynomial.X_dvd_X] using hij

/-- Specialization of the two-chart intersection result to distinct variables
of a polynomial ring over a field. -/
theorem polynomial_variable_localizations_inf_eq_bot
    (K : Type*) [Field K] [Algebra (MvPolynomial σ k) K]
    [IsFractionRing (MvPolynomial σ k) K] {i j : σ} (hij : i ≠ j) :
    awayInFractionField K (MvPolynomial.X i : MvPolynomial σ k) (MvPolynomial.X_ne_zero i) ⊓
      awayInFractionField K (MvPolynomial.X j : MvPolynomial σ k) (MvPolynomial.X_ne_zero j) = ⊥ := by
  exact awayInFractionField_inf_eq_bot K (MvPolynomial.X_ne_zero i) (MvPolynomial.X_ne_zero j)
    (isRelPrime_X_of_ne hij)

end PolynomialVariables

end StableCoordinate

end OAI
