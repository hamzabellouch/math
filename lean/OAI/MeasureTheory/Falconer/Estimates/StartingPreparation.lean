import OAI.MeasureTheory.Falconer.Estimates.OddPreparedPair

namespace OAI

/-! # Starting-pair preparation in every ambient dimension

This is `prep:starting-pairs`. It preserves the original distances in the
classical-plane alternative, and fixes the Frostman gap and pair before
choosing the later coarse partition parameter.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem prepared_original_pair_or_positive_distance
    (hFrostman : PublishedFrostmanAboveHalf) (hClassical : PublishedClassicalDistance)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {d : ℕ} (hd : 2 ≤ d) (E : Set (Space d)) (hE : IsCompact E)
    (hDim : (d:ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
    0 < volume (distanceSet E) ∨ Nonempty (PreparedOriginalPair E ε) := by
  by_cases heven : d % 2 = 0
  · obtain ⟨h,hh,rfl⟩ : ∃ h : ℕ, 1 ≤ h ∧ d = 2*h :=
      ⟨d/2,by omega,by omega⟩
    exact Or.inr (even_prepared_original_pair hFrostman hR hh E hE hDim hε)
  · obtain ⟨h,rfl⟩ : ∃ h : ℕ, d = 2*h+3 := ⟨(d-3)/2,by omega⟩
    exact odd_prepared_original_pair_or_positive_distance
      hFrostman hClassical hR hH hF hLW E hE hDim hε

end Falconer

end OAI
