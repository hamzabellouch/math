import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Localization.AtPrime.Basic

namespace OAI

universe uR uK

/-!
# Recovering a global coefficient from its local representations

The denominator-ideal argument works in any commutative algebra. It identifies
the intersection of maximal localizations inside a fraction field with the
base ring, both as subalgebra membership and through actual local elements.
-/

namespace CirculantHadamard

/-- If every maximal ideal admits a denominator outside it taking `z` into the
base ring's image, then `z` itself lies in that image. -/
theorem exists_base_of_local_denominators
    {R : Type uR} {K : Type uK} [CommRing R] [CommRing K] [Algebra R K]
    (z : K)
    (hz : ∀ m : MaximalSpectrum R, ∃ a s : R,
      s ∉ m.asIdeal ∧ algebraMap R K s * z = algebraMap R K a) :
    ∃ r : R, algebraMap R K r = z := by
  classical
  by_contra h
  let denom : Ideal R :=
    (1 : Submodule R K).comap (LinearMap.toSpanSingleton R K z)
  have hdenom : (1 : R) ∉ denom := by
    simpa [denom] using h
  obtain ⟨m, hm, hle⟩ :=
    denom.exists_le_maximal (denom.ne_top_iff_one.mpr hdenom)
  obtain ⟨a, s, hs, hsa⟩ := hz ⟨m, hm⟩
  apply hs
  apply hle
  change s • z ∈ (1 : Submodule R K)
  apply Submodule.mem_one.mpr
  exact ⟨a, by simpa only [Algebra.smul_def] using hsa.symm⟩

section FractionField

variable {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Membership in every maximal localization, realized inside a common fraction
field, gives a base-ring representative. -/
theorem exists_base_of_mem_all_maximal_localizations
    {z : K}
    (hz : ∀ m : MaximalSpectrum R,
      z ∈ Localization.subalgebra.ofField K m.asIdeal.primeCompl
        m.asIdeal.primeCompl_le_nonZeroDivisors) :
    ∃ r : R, algebraMap R K r = z := by
  have hzall : z ∈ (⨅ m : MaximalSpectrum R,
      Localization.subalgebra.ofField K m.asIdeal.primeCompl
        m.asIdeal.primeCompl_le_nonZeroDivisors) :=
    Algebra.mem_iInf.mpr hz
  rw [MaximalSpectrum.iInf_localization_eq_bot R K] at hzall
  exact Algebra.mem_bot.mp hzall

/-- A fraction-field element represented by an actual element of each maximal
local ring is the image of a base-ring element. -/
theorem exists_base_of_localization_images
    {z : K}
    (hz : ∀ m : MaximalSpectrum R, ∃ y : Localization.AtPrime m.asIdeal,
      Localization.mapToFractionRing K m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal)
        m.asIdeal.primeCompl_le_nonZeroDivisors y = z) :
    ∃ r : R, algebraMap R K r = z := by
  apply exists_base_of_mem_all_maximal_localizations
  intro m
  obtain ⟨y, hy⟩ := hz m
  change ∃ (a s : R) (_ : s ∈ m.asIdeal.primeCompl),
    z = algebraMap R K a * (algebraMap R K s)⁻¹
  exact (Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField
    K m.asIdeal.primeCompl m.asIdeal.primeCompl_le_nonZeroDivisors
    (Localization.AtPrime m.asIdeal) z).mp ⟨y, hy⟩

end FractionField

end CirculantHadamard

end OAI
