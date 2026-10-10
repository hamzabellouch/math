import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTNoSmallCount
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFinalBinCount
import OAI.NumberTheory.TwoPoint.Halasz.HalaszSparseCost

namespace OAI

/-! The actual final original band gives the cardinality needed by the
integer-kernel estimate on every separated subset of the no-small class. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem mrt_no_small_card_at_scale :
    ∀ᶠ L : ℝ in Filter.atTop,
    ∀ (V : ℕ → Finset ℕ) (F : ℕ → ℂ), OneBounded F →
    ∀ J j : ℕ, j < J → ∀ P Q : ℝ, 1 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
    2 ≤ mrtBaseResolution P Q (1/100) →
    (∀ p ∈ V (j+1), p.Prime) →
    (∀ p ∈ V (j+1), mrtBandLower P Q (j+1) ≤ (p:ℝ) ∧
      (p:ℝ) ≤ mrtBandUpper Q (j+1)) →
    200*Real.log L+1 ≤ Real.log (mrtBandLower P Q (j+1)) →
    Real.log (mrtBandUpper Q (j+1)) ≤ Real.sqrt L →
    ∀ T : ℝ, 1 < T → T ≤ Real.exp L → ∀ S : Finset ℝ,
    (∀ t ∈ S, |t| ≤ T) →
    (∀ t ∈ S, ∀ s ∈ S, t≠s → 1 ≤ |t-s|) →
    (∀ t ∈ S, t ∈ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
      (mrtLogFamilyPolynomial V F P Q (1/100))
      (mrtLogFamilyThreshold P Q (1/100)) J) →
    (S.card:ℝ) ≤ Real.exp ((249/500:ℝ)*L) := by
  filter_upwards [mrt_no_small_final_samples,mrt_final_bin_count] with L hs hk
  intro V F hF J j hj P Q hP hPQ hQ hres hp hrange hlo hhi T hT hTU S hfreq hsep hno
  exact halasz_no_small_card_budget
    (hs V F hF J j hj P Q hQ hres hp hrange hlo hhi T hT hTU S hfreq hsep hno)
    (hk P Q (1/100) hP hPQ hQ (by norm_num) j hhi)

end TwoPointCorrelations

end OAI
