import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

universe uR

/-!
# Principal maximal ideals and local factor divisibility

A nonzero principal maximal ideal in a Noetherian local domain gives a DVR
and uniformizer factorizations. Its canonical additive valuation, valued in
`ℕ∞`, splits a product of a prime power and a unit.
-/

noncomputable section

namespace CirculantHadamard.LocalDVR

open IsLocalRing IsDiscreteValuationRing

section PrincipalMaximalIdeal

variable {R : Type uR} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

/-- A nonzero generator of the maximal ideal of a Noetherian local domain
proves that the ring is a DVR. -/
theorem isDiscreteValuationRing_of_maximalIdeal_eq_span {π : R}
    (hπ : π ≠ 0) (hspan : maximalIdeal R = Ideal.span {π}) :
    IsDiscreteValuationRing R := by
  have hmax : maximalIdeal R ≠ ⊥ := by
    intro hzero
    apply hπ
    exact Ideal.span_singleton_eq_bot.mp (hspan.symm.trans hzero)
  have hfield : ¬ IsField R := isField_iff_maximalIdeal_eq.not.mpr hmax
  have hprincipal : (maximalIdeal R).IsPrincipal := ⟨⟨π, hspan⟩⟩
  exact ((IsDiscreteValuationRing.TFAE R hfield).out 5 1).mp hprincipal

/-- The actual chosen generator factors every nonzero element into a unit
times a natural power. -/
theorem eq_unit_mul_pow_of_maximalIdeal_eq_span {π x : R}
    (hπ : π ≠ 0) (hspan : maximalIdeal R = Ideal.span {π}) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), x = (u : R) * π ^ n := by
  let : IsDiscreteValuationRing R :=
    isDiscreteValuationRing_of_maximalIdeal_eq_span hπ hspan
  exact eq_unit_mul_pow_irreducible hx ((irreducible_iff_uniformizer π).mpr hspan)

end PrincipalMaximalIdeal

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Normalize the additive valuation using the concrete uniformizer relation. -/
theorem addVal_eq_of_unit_mul_uniformizer_pow {π p : R} {u : Rˣ} {D : ℕ}
    (hspan : maximalIdeal R = Ideal.span {π}) (hp : p = (u : R) * π ^ D) :
    addVal R p = (D : ℕ∞) :=
  addVal_def p u ((irreducible_iff_uniformizer π).mpr hspan) D hp

/-- Right-unit version, convenient for the factorization of a rational prime. -/
theorem addVal_eq_of_uniformizer_pow_mul_unit {π p b : R} {D : ℕ}
    (hspan : maximalIdeal R = Ideal.span {π}) (hb : IsUnit b)
    (hp : p = π ^ D * b) : addVal R p = (D : ℕ∞) := by
  obtain ⟨u, rfl⟩ := hb
  exact addVal_eq_of_unit_mul_uniformizer_pow hspan (hp.trans (mul_comm _ _))

private theorem finite_add_eq {a b : ℕ∞} {N : ℕ} (h : a + b = (N : ℕ∞)) :
    ∃ m n : ℕ, a = (m : ℕ∞) ∧ b = (n : ℕ∞) ∧ m + n = N := by
  have ha : a ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_right zero_le
  have hb : b ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_left zero_le
  obtain ⟨m, hm, _⟩ := ENat.le_natCast_iff.mp ha
  obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp hb
  refine ⟨m, n, hm, hn, ?_⟩
  rw [hm, hn, ← Nat.cast_add] at h
  exact_mod_cast h

/-- If the valuation of a product is at least twice that of `p`, one factor
is divisible by `p`. The value of `p` is allowed to be ramified. -/
theorem dvd_or_dvd_of_mul_eq_pow_mul_unit {p x y b : R} {D e : ℕ}
    (_hp : p ≠ 0) (_hD : 0 < D) (hpval : addVal R p = (D : ℕ∞))
    (he : 2 ≤ e) (hb : IsUnit b) (hxy : x * y = p ^ e * b) :
    p ∣ x ∨ p ∣ y := by
  have hv := congrArg (addVal R) hxy
  rw [addVal_mul, addVal_mul, addVal_pow, hpval,
    addVal_eq_zero_iff.mpr hb, add_zero] at hv
  have hv' : addVal R x + addVal R y = ((e * D : ℕ) : ℕ∞) := by
    simpa only [nsmul_eq_mul, Nat.cast_mul] using hv
  obtain ⟨m, n, hm, hn, hmn⟩ := finite_add_eq hv'
  have heD : 2 * D ≤ e * D := Nat.mul_le_mul_right D he
  have hsplit : D ≤ m ∨ D ≤ n := by omega
  rcases hsplit with hx | hy
  · left
    apply addVal_le_iff_dvd.mp
    rw [hpval, hm]
    exact_mod_cast hx
  · right
    apply addVal_le_iff_dvd.mp
    rw [hpval, hn]
    exact_mod_cast hy

/-- A product with valuation one has a unit factor. This is the unramified
base case of the integral division argument. -/
theorem isUnit_or_isUnit_of_mul_eq_uniformizer_mul_unit {p x y b : R}
    (hpval : addVal R p = 1) (hb : IsUnit b) (hxy : x * y = p * b) :
    IsUnit x ∨ IsUnit y := by
  have hv := congrArg (addVal R) hxy
  rw [addVal_mul, addVal_mul, hpval, addVal_eq_zero_iff.mpr hb, add_zero] at hv
  obtain ⟨m, n, hm, hn, hmn⟩ := finite_add_eq (N := 1) hv
  have hsplit : m = 0 ∨ n = 0 := by omega
  rcases hsplit with hx | hy
  · left
    apply addVal_eq_zero_iff.mp
    simpa only [hx, Nat.cast_zero] using hm
  · right
    apply addVal_eq_zero_iff.mp
    simpa only [hy, Nat.cast_zero] using hn

end Valuation

end CirculantHadamard.LocalDVR

end

end OAI
