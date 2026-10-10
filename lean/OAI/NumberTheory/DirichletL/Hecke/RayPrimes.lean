import OAI.NumberTheory.DirichletL.Hecke.RayFamily
import OAI.NumberTheory.DirichletL.PrimeCounting.RayAsymptotic
import OAI.NumberTheory.DirichletL.PrimeCounting.IdealPrimeMass

namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.HeckeRayPrimes
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem analytic_family : PNT.RayAsymptotic.AnalyticFamily M
    (fun χ => LFunction (HeckeRayFamily.character M χ))
    (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1) 1) := by
  refine ⟨?_, ?_, ?_, ?_, HeckeRayFamily.principal_pole_ne_zero M⟩
  · intro χ s hs
    exact LFunction_eq_series _ hs
  · intro χ s hs hpole
    rcases hpole with hχ | hs1
    · exact (HeckeRayFamily.character_entire M χ hχ).analyticAt s
    · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
      filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1] with z hz0 hz1
      exact LFunction_differentiableAt _ hz0 (Or.inl hz1)
  · intro χ s hs hpole
    exact HeckeRayFamily.character_boundary_ne_zero M χ hs hpole.symm
  · apply PNT.RayAsymptotic.principalRegularization_analyticAt_of_local
      _ (HeckeOrigin.poleRemoved (HeckeRayFamily.character M 1))
      ((HeckeOrigin.poleRemoved_entire _).analyticAt 1)
    filter_upwards [isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with s hs0
    intro hs1
    exact (HeckeOrigin.poleRemoved_eq _ hs0 hs1).symm

theorem classCoeff_ratio_tendsto :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.classCoeff M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.classCoeff_ratio_tendsto M (analytic_family M)

theorem quotientClassCoeff_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => cumsum (PNT.RayAsymptotic.quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.RayAsymptotic.quotientClassCoeff_ratio_tendsto M H hH (analytic_family M)

theorem primeLogMass_ratio_tendsto :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayOrthogonality.principalIdeals M) N / N)
      atTop (𝓝 ((RayOrthogonality.rayCard M : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (classCoeff_ratio_tendsto M)

theorem quotientPrimeLogMass_ratio_tendsto
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H) :
    Tendsto (fun N : ℕ => PNT.IdealPrimeMass.primeLogMass (RayQuotient.identityClass M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) :=
  PNT.IdealPrimeMass.primeLogMass_ratio_tendsto _ (quotientClassCoeff_ratio_tendsto M H hH)

end SevenEighths.HeckeRayPrimes

end

end OAI
