import OAI.MeasureTheory.Falconer.Estimates.SevenInputsMain
import OAI.MeasureTheory.Falconer.Estimates.StartingDescent

namespace OAI

/-! # Removing the classical-threshold input by strict dimension descent

The charged affine plane has smaller dimension than the original space.
Its distance conclusion therefore follows from the induction hypothesis.
The planar base case and the higher-dimensional analytic proof stay separate.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem mainTarget_of_six_published_inputs
    (hPlanar : PlanarFalconer.PublishedPlanarRadialMoment)
    (hFrostman : PublishedFrostmanAboveHalf)
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd E hE hDim
    have hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
        (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K) := by
      intro k hk
      exact ih k hk
    by_cases htwo : d = 2
    · subst d
      have he : (2 : ℝ≥0∞)/2 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
      have hh : (1 : ℝ≥0∞) < dimH E := by simpa only [Nat.cast_ofNat,he] using hDim
      exact planar_case_of_published_radial hPlanar E hE hh
    · obtain ⟨m,rfl⟩ : ∃ m : ℕ, d = m+3 := ⟨d-3,by omega⟩
      rcases prepared_pair_of_lower_dimensions hFrostman hRadial hHeavy hFurstenberg
        published_finite_loomis_whitney hmain hd E hE hDim
        (by norm_num : (0:ℝ) < 1/8) with hpos | hp
      · exact hpos
      · obtain ⟨p⟩ := hp
        exact prepared_pair_positive_distance published_gnomonic_surface hQuadratic m E hE p

theorem classical_distance_of_six_published_inputs
    (hPlanar : PlanarFalconer.PublishedPlanarRadialMoment)
    (hFrostman : PublishedFrostmanAboveHalf)
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : PublishedClassicalDistance := by
  intro n hn K hK hDim
  apply mainTarget_of_six_published_inputs hPlanar hFrostman hRadial hHeavy hFurstenberg hQuadratic n hn K hK
  have he : (n : ℝ≥0∞)/2 = ENNReal.ofReal ((n:ℝ)/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_natCast]
    norm_num
  rw [he]
  apply lt_of_le_of_lt _ hDim
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Falconer

end OAI
