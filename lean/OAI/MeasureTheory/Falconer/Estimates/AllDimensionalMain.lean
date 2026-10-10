import OAI.MeasureTheory.Falconer.Estimates.ConditionalPlanar
import OAI.MeasureTheory.Falconer.Shells.PreparedEndgame

namespace OAI

/-! # The all-dimensional main theorem, conditional on published inputs

The planar branch uses the planar Fourier-energy argument. Every
higher-dimensional branch uses original-pair preparation, angular and
graph estimates, and scalar reconstruction. Published inputs remain
explicit arguments.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem mainTarget_of_published_inputs
    (hPlanar : PlanarFalconer.PublishedPlanarRadialMoment)
    (hFrostman : PublishedFrostmanAboveHalf)
    (hClassical : PublishedClassicalDistance)
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hLoomisWhitney : PublishedFiniteLoomisWhitney)
    (hGnomonic : PublishedGnomonicSurface)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget := by
  intro d hd E hE hDim
  by_cases htwo : d = 2
  · subst d
    have he : (2 : ℝ≥0∞)/2 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
    have hh : (1 : ℝ≥0∞) < dimH E := by simpa only [Nat.cast_ofNat,he] using hDim
    exact planar_case_of_published_radial hPlanar E hE hh
  · obtain ⟨m,rfl⟩ : ∃ m : ℕ, d = m+3 := ⟨d-3,by omega⟩
    rcases prepared_original_pair_or_positive_distance hFrostman hClassical hRadial
      hHeavy hFurstenberg hLoomisWhitney (by omega) E hE hDim
      (by norm_num : (0:ℝ) < 1/8) with hpos | hp
    · exact hpos
    · obtain ⟨p⟩ := hp
      exact prepared_pair_positive_distance hGnomonic hQuadratic m E hE p

end Falconer

end OAI
