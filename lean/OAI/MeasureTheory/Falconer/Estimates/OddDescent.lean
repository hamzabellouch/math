import OAI.MeasureTheory.Falconer.Estimates.DimensionDescent
import OAI.MeasureTheory.Falconer.Estimates.OddPreparedPair

namespace OAI

/-! # Odd-dimensional preparation using only lower-dimensional main statements -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem odd_prepared_pair_of_lower_dimensions
    (hFrostman : PublishedFrostmanAboveHalf)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ}
    (hmain : ∀ k : ℕ, k < 2*h+3 → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
      (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K))
    (E : Set (Space (2*h+3))) (hE : IsCompact E)
    (hDim : ((2*h+3:ℕ):ℝ≥0∞)/2 < dimH E) {ε : ℝ} (hε : 0 < ε) :
    0 < volume (distanceSet E) ∨ Nonempty (PreparedOriginalPair E ε) := by
  obtain ⟨s,hs,_,μ,hμE,C,hC,hfrost⟩ :=
    hFrostman (2*h+3) (by omega) E hE hDim
  have hs' : (h:ℝ)+3/2 < s := by push_cast at hs; linarith
  have hsupp : (μ : Measure (Space (2*h+3))).support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed hμE
  by_cases hnull : ∀ x : Space (2*h+3), ∀ V : Submodule ℝ (Space (2*h+3)),
      Module.finrank ℝ V ≤ h+2 → (μ : Measure (Space (2*h+3))) {y | y-x ∈ V} = 0
  · exact Or.inr (odd_noncharging_prepared_original_pair hR hH hF hLW
      E hE μ hμE hs' hfrost hnull hε)
  · push Not at hnull
    obtain ⟨x,V,hV,hcharge⟩ := hnull
    have hVr : (Module.finrank ℝ V:ℝ) ≤ (h:ℝ)+2 := by exact_mod_cast hV
    have hthreshold : ((Module.finrank ℝ V:ℝ)+1)/2 < s := by
      nlinarith [show (0:ℝ) ≤ (h:ℝ) by positivity]
    have hdist := charged_plane_distance_of_lower_dimensions hmain μ
      (hE.of_isClosed_subset Measure.isClosed_support hsupp) V (by omega) x
      (pos_iff_ne_zero.mpr hcharge) hthreshold hC hfrost
    exact Or.inl (hdist.trans_le (measure_mono (distanceSet_mono hsupp)))


end Falconer

end OAI
