import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Int

namespace OAI

universe uA uB

/-!
# Maps between coefficient localizations and maximal ideals over primes

The localization map uses the actual contraction of the target prime ideal.
Its denominator condition follows from the definition of contraction; no
integrality is needed for this map. Integrality is used separately to prove
maximality of contractions and existence of maximal ideals over rational primes.
-/

namespace CirculantHadamard

section LocalizationMap

variable {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]

/-- The actual map from the localization at a contracted prime ideal. -/
noncomputable def localizationAtComapMap (f : A →+* B) (m : Ideal B) [m.IsPrime] :
    Localization.AtPrime (m.comap f) →+* Localization.AtPrime m :=
  Localization.localRingHom (m.comap f) m f rfl

/-- The induced map agrees with the original ring map on coefficients. -/
@[simp] theorem localizationAtComapMap_algebraMap (f : A →+* B)
    (m : Ideal B) [m.IsPrime] (a : A) :
    localizationAtComapMap f m (algebraMap A (Localization.AtPrime (m.comap f)) a) =
      algebraMap B (Localization.AtPrime m) (f a) :=
  Localization.localRingHom_to_map (m.comap f) m f rfl a

/-- Both numerator and denominator follow the coefficient inclusion. -/
theorem localizationAtComapMap_mk' (f : A →+* B) (m : Ideal B) [m.IsPrime]
    (a : A) (s : (m.comap f).primeCompl) :
    localizationAtComapMap f m (IsLocalization.mk' (Localization.AtPrime (m.comap f)) a s) =
      IsLocalization.mk' (Localization.AtPrime m) (f a)
        (⟨f s, s.2⟩ : m.primeCompl) :=
  Localization.localRingHom_mk' (m.comap f) m f rfl a s

/-- An inclusion into a domain remains injective after the two prime
localizations, even though the target inverts additional denominators. -/
theorem localizationAtComapMap_injective [IsDomain B] (f : A →+* B)
    (hf : Function.Injective f) (m : Ideal B) [m.IsPrime] :
    Function.Injective (localizationAtComapMap f m) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := (m.comap f).primeCompl) (Localization.AtPrime (m.comap f))
    (localizationAtComapMap f m)
  intro a ha
  rw [localizationAtComapMap_algebraMap] at ha
  have hB : Function.Injective (algebraMap B (Localization.AtPrime m)) :=
    IsLocalization.injective (Localization.AtPrime m) m.primeCompl_le_nonZeroDivisors
  have hfa : f a = 0 := hB (by simpa only [map_zero] using ha)
  have haz : a = 0 := hf (by simpa only [map_zero] using hfa)
  rw [haz, map_zero]

/-- Units used by the local comparison remain units in the larger
coefficient localization. -/
theorem localizationAtComapMap_isUnit (f : A →+* B) (m : Ideal B) [m.IsPrime]
    {x : Localization.AtPrime (m.comap f)} (hx : IsUnit x) :
    IsUnit (localizationAtComapMap f m x) :=
  hx.map (localizationAtComapMap f m)

/-- Integral coefficient extensions preserve maximality on contraction. -/
theorem maximal_comap_of_integral (f : A →+* B) (hf : f.IsIntegral)
    (m : Ideal B) [m.IsMaximal] : (m.comap f).IsMaximal :=
  Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf m

end LocalizationMap

/-- Every rational prime has a maximal ideal above it in an integral
integer algebra with injective integer map. The conclusion retains the exact
contraction as well as membership of the prime in the maximal ideal. -/
theorem exists_maximal_ideal_over_nat_prime (B : Type uB) [CommRing B]
    [Algebra ℤ B] [Algebra.IsIntegral ℤ B]
    (hB : Function.Injective (algebraMap ℤ B)) {p : ℕ} (hp : p.Prime) :
    ∃ m : Ideal B, m.IsMaximal ∧
      m.comap (algebraMap ℤ B) = Ideal.span ({(p : ℤ)} : Set ℤ) ∧ (p : B) ∈ m := by
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible
  have hker : RingHom.ker (algebraMap ℤ B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hB
  obtain ⟨m, hm, hcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := B) P
      (by rw [hker]; exact bot_le)
  refine ⟨m, hm, hcomap, ?_⟩
  have hpP : (p : ℤ) ∈ P := Ideal.subset_span (Set.mem_singleton _)
  have hpcomap : (p : ℤ) ∈ m.comap (algebraMap ℤ B) := by
    change (p : ℤ) ∈ m.under ℤ
    rwa [hcomap]
  have hpm := Ideal.mem_comap.mp hpcomap
  simpa only [map_natCast] using hpm

/-- Characteristic zero supplies the injective integer map automatically. -/
theorem exists_maximal_ideal_over_nat_prime_of_charZero (B : Type uB) [CommRing B]
    [CharZero B] [Algebra ℤ B] [Algebra.IsIntegral ℤ B] {p : ℕ} (hp : p.Prime) :
    ∃ m : Ideal B, m.IsMaximal ∧
      m.comap (algebraMap ℤ B) = Ideal.span ({(p : ℤ)} : Set ℤ) ∧ (p : B) ∈ m :=
  exists_maximal_ideal_over_nat_prime B (algebraMap ℤ B).injective_int hp

end CirculantHadamard

end OAI
