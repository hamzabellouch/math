import OAI.LinearAlgebra.CirculantHadamard.BinaryLocalization
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicRings
import Mathlib.RingTheory.Localization.AsSubring

namespace OAI

/-!
# One concrete local ring and residue field

For the actual cyclotomic coefficient algebra `B u`, choose a maximal ideal
containing two. Both first-order calculations use the same localization and
the same residue field. The choices depend only on `u`, not on a character or
on which of the three norm elements is being considered.
-/

noncomputable section

namespace CirculantHadamard.BinaryLocalRing

open CyclotomicRings

def twoIdeal (u : ℕ) : Ideal (B u) :=
  Classical.choose (BinaryLocalization.exists_maximal_two_mem (B u))

instance twoIdeal_isMaximal (u : ℕ) : (twoIdeal u).IsMaximal :=
  (Classical.choose_spec (BinaryLocalization.exists_maximal_two_mem (B u))).1

theorem two_mem (u : ℕ) : (2 : B u) ∈ twoIdeal u :=
  (Classical.choose_spec (BinaryLocalization.exists_maximal_two_mem (B u))).2

abbrev O (u : ℕ) := Localization.AtPrime (twoIdeal u)

/- Name the canonical localization algebra directly. This avoids searching
through iterated-localization algebra instances for these concrete carriers. -/
instance local_algebra (u : ℕ) : Algebra (B u) (O u) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := (twoIdeal u).primeCompl)

instance fraction_algebra (u : ℕ) : Algebra (B u) (FractionRing (B u)) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := nonZeroDivisors (B u))

abbrev k (u : ℕ) := IsLocalRing.ResidueField (O u)

def toLocal (u : ℕ) : B u →+* O u := algebraMap (B u) (O u)

theorem toLocal_injective (u : ℕ) : Function.Injective (toLocal u) :=
  IsLocalization.injective (O u) (twoIdeal u).primeCompl_le_nonZeroDivisors

/-- The same localization embeds into the fraction field used for the
alternating products. -/
def toFraction (u : ℕ) : O u →ₐ[B u] FractionRing (B u) :=
  Localization.mapToFractionRing (FractionRing (B u)) (twoIdeal u).primeCompl
    (O u) (twoIdeal u).primeCompl_le_nonZeroDivisors

@[simp] theorem toFraction_toLocal (u : ℕ) (x : B u) :
    toFraction u (toLocal u x) = algebraMap (B u) (FractionRing (B u)) x :=
  (toFraction u).commutes x

theorem toFraction_injective (u : ℕ) : Function.Injective (toFraction u) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (twoIdeal u).primeCompl (toFraction u).toRingHom).2
  intro a b
  change toLocal u a = toLocal u b ↔
    toFraction u (toLocal u a) = toFraction u (toLocal u b)
  rw [toFraction_toLocal, toFraction_toLocal]
  constructor
  · intro h
    exact congrArg (algebraMap (B u) (FractionRing (B u))) (toLocal_injective u h)
  · intro h
    exact congrArg (toLocal u) (IsFractionRing.injective (B u) (FractionRing (B u)) h)

instance local_charZero (u : ℕ) : CharZero (O u) where
  cast_injective a b hab := by
    apply (Nat.cast_injective (R := B u))
    apply toLocal_injective u
    simpa only [map_natCast] using hab

instance residue_charTwo (u : ℕ) : CharP (k u) 2 :=
  BinaryLocalization.residue_char_two (twoIdeal u) (two_mem u)

def residue (u : ℕ) : O u →+* k u := IsLocalRing.residue (O u)

def gaussianToLocal (u : ℕ) : GaussianRing →+* O u :=
  (toLocal u).comp (gaussianToB u).toRingHom

def imaginary (u : ℕ) : O u := gaussianToLocal u gaussianI

theorem imaginary_sq (u : ℕ) : imaginary u ^ 2 = -1 := by
  unfold imaginary
  rw [← map_pow, gaussianI_sq, map_neg, map_one]

theorem residue_imaginary (u : ℕ) : residue u (imaginary u) = 1 :=
  BinaryLocalization.map_i_eq_one (residue u) (imaginary u) (imaginary_sq u)

theorem two_ne_zero (u : ℕ) : (2 : O u) ≠ 0 :=
  Nat.cast_ne_zero.mpr (by decide)

/-- Every one of the actual character norms supplies its own local unit. -/
theorem norm_isUnit (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) : IsUnit (toLocal u x) := by
  apply BinaryLocalization.isUnit_of_mul_eq_odd_square hu
    (y := toLocal u y)
  have h := congrArg (toLocal u) hxy
  simpa only [map_mul, map_pow, map_natCast] using h

/-- The unit value is the localized character value, not an unrelated witness. -/
def normUnit (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) : (O u)ˣ :=
  (norm_isUnit u hu x y hxy).unit

@[simp] theorem normUnit_val (u : ℕ) (hu : Odd u) (x y : B u)
    (hxy : x * y = (u : B u) ^ 2) :
    (normUnit u hu x y hxy : O u) = toLocal u x :=
  (norm_isUnit u hu x y hxy).unit_spec

end CirculantHadamard.BinaryLocalRing

end

end OAI
