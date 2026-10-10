import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedBoundary
import OAI.Probability.InvariantIsing.Magnetic.MagneticWeightedSpatial
import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabClosedDerivatives

namespace OAI

/-! Closed-strip derivative data for the weighted continuation. At either
spin endpoint the continued function is identically zero in time. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticWeightedSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarWeightedSlope L hL A ζ p.1 p.2 else 0

def closedMagneticWeightedSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarWeightedSecond L hL A ζ p.1 p.2 else 0

def closedMagneticWeightedPotential (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarWeightedPotential L hL ζ p.1 p.2 else 0

def closedMagneticWeightedTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  (closedMagneticScalarCurvature L hL ζ p) ^ 2 / 2 *
    closedMagneticWeightedSecond L hL A ζ p +
      closedMagneticWeightedPotential L hL ζ p *
        closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ p

lemma closedMagneticSlabWeighted_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ (v, u))
      (closedMagneticWeightedSlope L hL A ζ (v, s)) s := by
  have he : (fun u => closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ (v, u))
      =ᶠ[𝓝 s] magneticScalarSlabWeighted L hL A.toMagneticContinuationJet ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticWeightedSlope, hs, ite_true] using
    (magneticScalarSlabWeighted_hasDerivAt_spin L hL A hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticWeightedSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticWeightedSlope L hL A ζ (v, u))
      (closedMagneticWeightedSecond L hL A ζ (v, s)) s := by
  have he : (fun u => closedMagneticWeightedSlope L hL A ζ (v, u))
      =ᶠ[𝓝 s] magneticScalarWeightedSlope L hL A ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticWeightedSecond, hs, ite_true] using
    (magneticScalarWeightedSlope_hasDerivAt_spin L hL A hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticSlabWeighted_hasDerivAt_time (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationFourJet)
    {ζ v : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (s : ℝ) :
    HasDerivAt (fun t => closedMagneticSlabWeighted L hL A.toMagneticContinuationJet ζ (t, s))
      (closedMagneticWeightedTime L hL A ζ (v, s)) v := by
  by_cases hs : |s| < 1
  · simpa only [closedMagneticSlabWeighted, closedMagneticWeightedTime,
      closedMagneticScalarCurvature, closedMagneticWeightedSecond,
      closedMagneticWeightedPotential, hs, ite_true] using
        magneticScalarSlabWeighted_PDE L hL A hζ hv hs
  · simpa only [closedMagneticSlabWeighted, closedMagneticWeightedTime,
      closedMagneticScalarCurvature, closedMagneticWeightedSecond,
      closedMagneticWeightedPotential, hs, ite_false, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, zero_mul, mul_zero, add_zero] using (hasDerivAt_const v (0 : ℝ))

lemma closedMagneticWeightedPotential_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (p : ℝ × ℝ) :
    closedMagneticWeightedPotential L hL ζ p ≤ magneticSlabPotentialCap L ζ + 2 := by
  by_cases hs : |p.2| < 1
  · exact (le_abs_self _).trans (by simpa only [closedMagneticWeightedPotential, hs,
      ite_true] using magneticScalarWeightedPotential_bound L hL hL1 hζ hζ1 hs p.1)
  · simp only [closedMagneticWeightedPotential, hs, ite_false]
    exact add_nonneg (add_nonneg (magneticFourthRatioCap_nonneg _) (sq_nonneg _)) (by norm_num)

end InvariantIsing

end

end OAI
