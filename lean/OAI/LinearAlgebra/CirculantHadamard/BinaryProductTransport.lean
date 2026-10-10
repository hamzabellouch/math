import OAI.LinearAlgebra.CirculantHadamard.AlternatingProducts
import OAI.LinearAlgebra.CirculantHadamard.BinaryLocalRing
import Mathlib.Algebra.Group.Units.Hom

namespace OAI

universe uG uI

/-!
# Odd-power products in the concrete binary local ring

The local units are supplied with their actual coefficient-ring values.
Their alternating product maps to the fixed alternating product in the
fraction field. Injectivity transports each exact power identity back to
the local units, with the same exponent.
-/

noncomputable section

namespace CirculantHadamard.BinaryProductTransport

open CyclotomicRings BinaryLocalRing

/-- Odd-power torsion is closed under taking a quotient in a commutative
group. The product of the two supplied exponents is an explicit witness. -/
theorem odd_power_mul_inv {G : Type uG} [CommGroup G] (x y : G)
    (hx : ∃ m : ℕ, 0 < m ∧ Odd m ∧ x ^ m = 1)
    (hy : ∃ n : ℕ, 0 < n ∧ Odd n ∧ y ^ n = 1) :
    ∃ r : ℕ, 0 < r ∧ Odd r ∧ (x * y⁻¹) ^ r = 1 := by
  obtain ⟨m, hm, hmOdd, hxm⟩ := hx
  obtain ⟨n, hn, hnOdd, hyn⟩ := hy
  refine ⟨m * n, Nat.mul_pos hm hn, hmOdd.mul hnOdd, ?_⟩
  have hxmn : x ^ (m * n) = 1 := by rw [pow_mul, hxm, one_pow]
  have hymn : y ^ (m * n) = 1 := by rw [Nat.mul_comm m n, pow_mul, hyn, one_pow]
  simp only [mul_pow, inv_pow, hxmn, hymn, inv_one, mul_one]

/-- The actual map from local units to the fraction field of `B u`. -/
def localUnitToFraction (u : ℕ) : (O u)ˣ →* FractionRing (B u) :=
  (toFraction u).toRingHom.toMonoidHom.comp (Units.coeHom (O u))

@[simp] theorem localUnitToFraction_apply (u : ℕ) (X : (O u)ˣ) :
    localUnitToFraction u X = toFraction u (X : O u) := rfl

theorem localUnitToFraction_injective (u : ℕ) :
    Function.Injective (localUnitToFraction u) := by
  intro X Y h
  apply Units.ext
  exact toFraction_injective u h

/-- Transport of the literal signed subset product, using the supplied
value equality only for subsets that occur in the product. -/
theorem local_alternatingProduct_toFraction {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S)) :
    localUnitToFraction u (alternatingProduct t X) =
      alternatingProduct t (fun S => algebraMap (B u) (FractionRing (B u)) (x S)) := by
  rw [map_alternatingProduct]
  apply alternatingProduct_congr
  intro S hS
  change toFraction u (X S : O u) = _
  rw [hX S hS, toFraction_toLocal]

/-- An exact fraction-field power identity holds for the actual local
alternating product with precisely the same exponent. -/
theorem local_alternatingProduct_pow_eq_one {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S)) (m : ℕ)
    (hpow : (alternatingProduct t
      (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1) :
    (alternatingProduct t X) ^ m = 1 := by
  apply localUnitToFraction_injective u
  rw [map_pow, map_one, local_alternatingProduct_toFraction u t x X hX]
  exact hpow

theorem local_alternatingProduct_has_odd_power {I : Type uI} (u : ℕ) (t : Finset I)
    (x : Finset I → B u) (X : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S))
    (hodd : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ (alternatingProduct t X) ^ m = 1 := by
  obtain ⟨m, hm, hmOdd, hpow⟩ := hodd
  exact ⟨m, hm, hmOdd, local_alternatingProduct_pow_eq_one u t x X hX m hpow⟩

/-- The two concrete unit families produce an odd-power quotient family.
No torsion of individual factors is assumed or inferred. -/
theorem local_alternatingProduct_ratio_has_odd_power {I : Type uI}
    (u : ℕ) (t : Finset I) (x y : Finset I → B u)
    (X Y : Finset I → (O u)ˣ)
    (hX : ∀ S ⊆ t, (X S : O u) = toLocal u (x S))
    (hY : ∀ S ⊆ t, (Y S : O u) = toLocal u (y S))
    (hx : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (x S))) ^ m = 1)
    (hy : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t
        (fun S => algebraMap (B u) (FractionRing (B u)) (y S))) ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧
      (alternatingProduct t (fun S => X S * (Y S)⁻¹)) ^ m = 1 := by
  simpa only [alternatingProduct_mul, alternatingProduct_inv] using
    odd_power_mul_inv (alternatingProduct t X) (alternatingProduct t Y)
      (local_alternatingProduct_has_odd_power u t x X hX hx)
      (local_alternatingProduct_has_odd_power u t y Y hY hy)

end CirculantHadamard.BinaryProductTransport

end

end OAI
