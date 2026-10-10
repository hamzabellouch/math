import Mathlib

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.IntersectionLength
noncomputable section
open IsLocalRing
variable (R : Type*) [CommRing R] [IsArtinianRing R]
variable (K : Type*) [Field K] [Algebra K R] [FiniteDimensional K R]

theorem finrank_eq_sum_localizations [Fintype (MaximalSpectrum R)] :
    Module.finrank K R = ∑ m : MaximalSpectrum R,
      Module.finrank K (Localization.AtPrime m.asIdeal) := by
  let : ∀ m : MaximalSpectrum R, Module.Finite K (Localization.AtPrime m.asIdeal) :=
    fun m => Module.Finite.of_surjective (IsScalarTower.toAlgHom K R
      (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  have e := (MaximalSpectrum.toPiLocalizationEquiv R).restrictScalars K
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

end
end MaximalSeshadri.IntersectionLength
end


end
end

end OAI
