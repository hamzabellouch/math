import OAI.MeasureTheory.Falconer.Estimates.PreparedPair
import OAI.MeasureTheory.Falconer.Estimates.OddNonchargingPreparation
import OAI.MeasureTheory.Falconer.Estimates.ChargedPlane

namespace OAI

/-! # The odd-dimensional preparation and the genuine classical-plane alternative -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem odd_noncharging_prepared_original_pair
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} (E : Set (Space (2*h+3))) (hE : IsCompact E)
    (μ : ProbabilityMeasure (Space (2*h+3)))
    (hμE : (μ : Measure (Space (2*h+3))) Eᶜ = 0)
    {s C ε : ℝ} (hs : (h:ℝ)+3/2 < s)
    (hfrost : FrostmanBallBound (μ : Measure (Space (2*h+3))) s C)
    (hnull : ∀ x : Space (2*h+3), ∀ V : Submodule ℝ (Space (2*h+3)),
      Module.finrank ℝ V ≤ h+2 → (μ : Measure (Space (2*h+3))) {y | y-x ∈ V} = 0)
    (hε : 0 < ε) : Nonempty (PreparedOriginalPair E ε) := by
  have hs' : ((h+2:ℕ):ℝ)-1/2 < s := by push_cast; linarith
  obtain ⟨δ,hδ,hδ1,ζ,hK,hdom,f,⟨p⟩⟩ :=
    choose_odd_projected_pieces (by omega : 2 ≤ h+2) μ hs' hfrost hnull hε
  have hα : (h:ℝ)+3/2 < ((h+2:ℕ):ℝ)-1/2+δ := by push_cast; linarith
  have hα' : ((h+2:ℕ):ℝ)-1/2+δ < (h:ℝ)+2 := by push_cast; linarith
  have hhalf : ((2*h+3:ℕ):ℝ)/2 = (h:ℝ)+3/2 := by push_cast; ring
  have hsupp : (μ : Measure (Space (2*h+3))).support ⊆ E :=
    Measure.support_subset_of_isClosed hE.isClosed hμE
  refine ⟨{
    auxiliaryDimension := h+3
    exponent := ((h+2:ℕ):ℝ)-1/2+δ
    exponent_gt := by rw [hhalf]; exact hα
    base := ζ
    pair := p.firstPair
    left_subset := (p.left_ac.trans hdom).support_mono.trans hsupp
    right_subset := (p.right_ac.trans hdom).support_mono.trans hsupp
    filters := ?_ }⟩
  intro ω hω hω1
  obtain ⟨Γ,hΓ,hanti,hpos,hsub,hcap,hpartition⟩ :=
    p.odd_original_caps_partition hR hH hF hLW hα hα' hω hω1
  refine ⟨Γ,hΓ,hanti,hpos,hsub,?_,?_⟩
  · intro N
    apply (hpartition N).mono_bound
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hdim : ((h+3:ℕ):ℝ) ≤ ((2*h+3:ℕ):ℝ) := by exact_mod_cast (by omega : h+3 ≤ 2*h+3)
    nlinarith only [mul_le_mul_of_nonneg_right hdim (mul_nonneg hω.le (Nat.cast_nonneg N))]
  · simpa only [hhalf, TwoProjectionPieces.firstPair] using hcap

theorem odd_prepared_original_pair_or_positive_distance
    (hFrostman : PublishedFrostmanAboveHalf) (hClassical : PublishedClassicalDistance)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    {h : ℕ} (E : Set (Space (2*h+3))) (hE : IsCompact E)
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
    have hdist := positive_distance_of_charged_affine_plane hClassical μ
      (hE.of_isClosed_subset Measure.isClosed_support hsupp) V x
      (pos_iff_ne_zero.mpr hcharge) hthreshold hC hfrost
    exact Or.inl (hdist.trans_le (measure_mono (distanceSet_mono hsupp)))

end Falconer

end OAI
