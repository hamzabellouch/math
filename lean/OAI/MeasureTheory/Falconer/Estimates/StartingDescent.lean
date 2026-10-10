import OAI.MeasureTheory.Falconer.Estimates.OddDescent

namespace OAI

/-! # Ambient preparation by strict dimension descent in the charged case -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem prepared_pair_of_lower_dimensions
    (hFrostman : PublishedFrostmanAboveHalf)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {d : ℕ}
    (hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (hd : 2 ≤ d) (E : Set (Space d)) (hE : IsCompact E)
    (hDim : (d:ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
    0 < volume (distanceSet E) ∨ Nonempty (PreparedOriginalPair E ε) := by
  by_cases heven : d % 2 = 0
  · obtain ⟨h,hh,rfl⟩ : ∃ h : ℕ, 1 ≤ h ∧ d = 2*h :=
      ⟨d/2,by omega,by omega⟩
    exact Or.inr (even_prepared_original_pair hFrostman hR hh E hE hDim hε)
  · obtain ⟨h,rfl⟩ : ∃ h : ℕ, d = 2*h+3 := ⟨(d-3)/2,by omega⟩
    exact odd_prepared_pair_of_lower_dimensions
      hFrostman hR hH hF hLW hmain E hE hDim hε


end Falconer

end OAI
