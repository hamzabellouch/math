import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic

namespace OAI

/-!
# Picard triviality for the factorial affine charts

Algebraic support for `bun:homotopy` in §4 of the source.  Over a GCD domain,
all invertible modules are trivial; in particular this applies to the UFD
localizations in the two charts and their polynomial extensions.

The statements below concern **invertible modules**, not just bijections of
underlying sets.  Invertible modules correspond to line bundles on an affine scheme.
-/

namespace StableCoordinate.PicardSupport

/-- An invertible module over a GCD domain admits a linear trivialization.
There is no Noetherian hypothesis: Mathlib's class-group theorem is stronger
than the particular source input. -/
theorem invertibleModule_trivial_of_gcd
    (A M : Type*) [CommRing A] [IsDomain A] [IsGCDMonoid A]
    [AddCommGroup M] [Module A M] [Module.Invertible A M] :
    Nonempty (M ≃ₗ[A] A) :=
  CommRing.Pic.mk_eq_one_iff.mp (Subsingleton.elim _ _)

/-- Triviality survives localization of a UFD at non-zero-divisors. -/
theorem invertibleModule_trivial_of_localization
    (A B M : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B]
    (hS : S ≤ nonZeroDivisors A)
    [AddCommGroup M] [Module B M] [Module.Invertible B M] :
    Nonempty (M ≃ₗ[B] B) := by
  let : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hS
  let : UniqueFactorizationMonoid B := UniqueFactorizationMonoid.of_isLocalization S B
  exact invertibleModule_trivial_of_gcd B M

/-- In particular, every invertible module on a principal localization of a
UFD at a nonzero element is trivial. -/
theorem invertibleModule_trivial_of_away
    (A B M : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing B] [Algebra A B] (a : A) [IsLocalization.Away a B] (ha : a ≠ 0)
    [AddCommGroup M] [Module B M] [Module.Invertible B M] :
    Nonempty (M ≃ₗ[B] B) :=
  invertibleModule_trivial_of_localization A B M (Submonoid.powers a)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha)

/-- The affine-line parameter used in the action-lift argument preserves
triviality of invertible modules on a factorial affine chart. -/
theorem invertibleModule_polynomial_trivial
    (A M : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [AddCommGroup M] [Module (Polynomial A) M] [Module.Invertible (Polynomial A) M] :
    Nonempty (M ≃ₗ[(Polynomial A)] (Polynomial A)) :=
  invertibleModule_trivial_of_gcd (Polynomial A) M

/-- Combined version for a principal affine chart and its affine-line extension. -/
theorem invertibleModule_away_polynomial_trivial
    (A B M : Type*) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [CommRing B] [Algebra A B] (a : A) [IsLocalization.Away a B] (ha : a ≠ 0)
    [AddCommGroup M] [Module (Polynomial B) M] [Module.Invertible (Polynomial B) M] :
    Nonempty (M ≃ₗ[(Polynomial B)] (Polynomial B)) := by
  let : IsDomain B := IsLocalization.Away.isDomain B ha
  let : UniqueFactorizationMonoid B :=
    UniqueFactorizationMonoid.of_isLocalization (Submonoid.powers a) B
  exact invertibleModule_polynomial_trivial B M

end StableCoordinate.PicardSupport

end OAI
