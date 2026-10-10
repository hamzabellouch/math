import OAI.LinearAlgebra.CirculantHadamard.LocalizationMaps
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace OAI

universe uB uO uk uF

/-!
# The characteristic-two local ring for the binary contradiction

The maximal ideal is constructed from an actual finite characteristic-zero
integer algebra.  Unit denominators follow from the odd norm identity, not
from an assumed extension of complex conjugation to a localization.
-/

namespace CirculantHadamard.BinaryLocalization

/-- A finite characteristic-zero integer algebra has a maximal ideal over two. -/
theorem exists_maximal_two_mem (B : Type uB) [CommRing B] [CharZero B]
    [Module.Finite ℤ B] :
    ∃ m : Ideal B, m.IsMaximal ∧ (2 : B) ∈ m := by
  let : Algebra.IsIntegral ℤ B := Algebra.IsIntegral.of_finite ℤ B
  obtain ⟨m, hm, _, htwo⟩ :=
    exists_maximal_ideal_over_nat_prime_of_charZero B Nat.prime_two
  exact ⟨m, hm, htwo⟩

/-- The one residue field used by both first-order maps has characteristic two. -/
theorem residue_char_two {B : Type uB} [CommRing B] (m : Ideal B) [m.IsPrime]
    (htwo : (2 : B) ∈ m) :
    CharP (IsLocalRing.ResidueField (Localization.AtPrime m)) 2 := by
  let O := Localization.AtPrime m
  apply CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
  have hmem : (2 : O) ∈ IsLocalRing.maximalIdeal O := by
    simpa only [map_ofNat] using
      (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (2 : B)).mpr htwo
  have hz := (IsLocalRing.residue_eq_zero_iff (2 : O)).mpr hmem
  simpa only [map_ofNat] using hz

/-- A square root of minus one reduces to one in a field of characteristic two. -/
theorem map_i_eq_one {O : Type uO} {k : Type uk} [CommRing O] [Field k] [CharP k 2]
    (φ : O →+* k) (i : O) (hi : i ^ 2 = -1) : φ i = 1 := by
  have htwo : (2 : k) = 0 := CharTwo.two_eq_zero
  have hsquare : (φ i) ^ 2 = -1 := by
    simpa using congrArg φ hi
  have hsq : (φ i - 1) ^ 2 = 0 := by
    calc
      (φ i - 1) ^ 2 = (φ i) ^ 2 - 2 * φ i + 1 := by ring
      _ = 0 := by rw [hsquare, htwo]; ring
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq)

/-- An odd scalar is one in the common characteristic-two residue field. -/
theorem map_odd_nat_eq_one {O : Type uO} {k : Type uk} [CommRing O] [Field k] [CharP k 2]
    (φ : O →+* k) {u : ℕ} (hu : Odd u) : φ (u : O) = 1 := by
  rw [map_natCast]
  exact natCast_eq_one_of_odd_of_two_eq_zero hu CharTwo.two_eq_zero

/-- The odd norm supplies a unit without requiring the second factor to be a
conjugation operation on the local ring. -/
theorem isUnit_of_mul_eq_odd_square {O : Type uO} [CommRing O] [IsLocalRing O]
    [CharP (IsLocalRing.ResidueField O) 2] {x y : O} {u : ℕ}
    (hu : Odd u) (hxy : x * y = (u : O) ^ 2) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  intro hx
  have h := congrArg (IsLocalRing.residue O) hxy
  have hu' := map_odd_nat_eq_one (IsLocalRing.residue O) hu
  have hbad : (0 : IsLocalRing.ResidueField O) = 1 := by
    simpa only [map_mul, map_pow, hx, zero_mul, hu', one_pow] using h
  exact zero_ne_one hbad

/-- A faithful ring embedding reflects the odd-power witness for an actual unit. -/
theorem odd_power_of_map {O : Type uO} {F : Type uF} [CommRing O] [CommRing F]
    (f : O →+* F) (hf : Function.Injective f) (u : Oˣ)
    (h : ∃ m : ℕ, 0 < m ∧ Odd m ∧ (f (u : O)) ^ m = 1) :
    ∃ m : ℕ, 0 < m ∧ Odd m ∧ u ^ m = 1 := by
  obtain ⟨m, hm, hodd, hpow⟩ := h
  refine ⟨m, hm, hodd, ?_⟩
  apply Units.ext
  apply hf
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] using hpow

end CirculantHadamard.BinaryLocalization

end OAI
