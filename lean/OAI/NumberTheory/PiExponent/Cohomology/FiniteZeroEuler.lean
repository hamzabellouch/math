import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.CurveZeroEuler

namespace OAI

noncomputable section
open scoped BigOperators
open AlgebraicGeometry PiExponentSeshadri.Geometry

namespace PiExponent.FiniteZeroEuler

theorem finrank_eq_sum_localizations
    (B : Type*) [CommRing B] [IsArtinianRing B]
    (F : Type*) [Field F] [Algebra F B] [Module.Finite F B]
    [Fintype (MaximalSpectrum B)] :
    Module.finrank F B = ∑ m : MaximalSpectrum B,
      Module.finrank F (Localization.AtPrime m.asIdeal) := by
  let : ∀ m : MaximalSpectrum B, Module.Finite F (Localization.AtPrime m.asIdeal) :=
    fun m => Module.Finite.of_surjective (IsScalarTower.toAlgHom F B
      (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  have e := (MaximalSpectrum.toPiLocalizationEquiv B).restrictScalars F
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

theorem finite_algebra_euler_eq_sum_local_lengths
    (B : Type) [CommRing B] [Algebra ℂ B] [Module.Finite ℂ B] (d : ℕ) :
    letI : IsArtinianRing B := IsArtinianRing.of_finite ℂ B
    letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
    eulerCharacteristic (CurveZeroEuler.algebraStructureMap B) d
      (structureSheaf (Spec (CommRingCat.of B))) =
        ∑ m : MaximalSpectrum B,
          ((Module.length (Localization.AtPrime m.asIdeal)
            (Localization.AtPrime m.asIdeal)).toNat : ℤ) := by
  let : IsArtinianRing B := IsArtinianRing.of_finite ℂ B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let : IsNoetherianRing B := isNoetherian_of_tower ℂ (inferInstance : IsNoetherian ℂ B)
  rw [CurveZeroEuler.affine_algebra_eulerCharacteristic,
    finrank_eq_sum_localizations B ℂ, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m _
  let : Module.Finite ℂ (Localization.AtPrime m.asIdeal) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom ℂ B
      (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  have h := PiExponentJets.W24.ring_length_eq_finrank_of_augmentation
    (CurveLocalOrder.residueAugmentation ℂ (Localization.AtPrime m.asIdeal))
    (CurveLocalOrder.residueAugmentation_algebraMap ℂ (Localization.AtPrime m.asIdeal))
  rw [h]
  simp

end PiExponent.FiniteZeroEuler

end

end OAI
