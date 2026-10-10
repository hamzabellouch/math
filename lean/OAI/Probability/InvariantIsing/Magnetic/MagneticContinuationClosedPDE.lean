import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationClosed

namespace OAI

/-! Closed-interval derivative data for finite inverse-coordinate square
continuations, with a zero second derivative chosen at the endpoints. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticContinuationSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarSlabContinuationSlope L hL A ζ p.1 p.2 else 0

def closedMagneticContinuationSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  if |p.2| < 1 then magneticScalarSlabContinuationSecond L hL A ζ p.1 p.2 else 0

def closedMagneticContinuationTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet) (ζ : ℝ)
    (p : ℝ × ℝ) : ℝ :=
  (closedMagneticScalarCurvature L hL ζ p) ^ 2 / 2 * closedMagneticContinuationSecond L hL A ζ p

lemma closedMagneticContinuation_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticContinuation L A ζ (v, u))
      (closedMagneticContinuationSlope L hL A ζ (v, s)) s := by
  have he : (fun u => closedMagneticContinuation L A ζ (v, u)) =ᶠ[𝓝 s]
      magneticScalarSlabContinuation L A ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticContinuationSlope, hs, ite_true] using
    (magneticScalarSlabContinuation_hasDerivAt_spin L hL A hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticContinuationSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticContinuationSlope L hL A ζ (v, u))
      (closedMagneticContinuationSecond L hL A ζ (v, s)) s := by
  have he : (fun u => closedMagneticContinuationSlope L hL A ζ (v, u)) =ᶠ[𝓝 s]
      magneticScalarSlabContinuationSlope L hL A ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticContinuationSecond, hs, ite_true] using
    (magneticScalarSlabContinuationSlope_hasDerivAt L hL A hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticContinuation_hasDerivAt_time (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (A : MagneticContinuationJet)
    {ζ v : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (s : ℝ) :
    HasDerivAt (fun t => closedMagneticContinuation L A ζ (t, s))
      (closedMagneticContinuationTime L hL A ζ (v, s)) v := by
  by_cases hs : |s| < 1
  · have hd := magneticScalarSlabContinuation_PDE L hL A hζ hs hv
    rw [magneticScalarSlabContinuation_second_deriv L hL A hζ hs v] at hd
    simpa only [closedMagneticContinuation, closedMagneticContinuationTime,
      closedMagneticScalarCurvature, closedMagneticContinuationSecond, hs, ite_true] using hd
  · simpa only [closedMagneticContinuation, closedMagneticContinuationTime,
      closedMagneticScalarCurvature, closedMagneticContinuationSecond, hs, ite_false,
      zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_mul] using (hasDerivAt_const v (1 : ℝ))

lemma closedMagneticSquareContinuationSecond_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (i : Fin (L.length + 1)) {ζ v : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (s : ℝ) :
    0 ≤ closedMagneticContinuationSecond L hL
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ (v, s) := by
  by_cases hs : |s| < 1
  · simpa only [closedMagneticContinuationSecond, hs, ite_true] using
      magneticScalarSlabSquare_second_nonneg L hL hL1 i hζ hζ1 hv hs
  · simp only [closedMagneticContinuationSecond, hs, ite_false, le_refl]

end InvariantIsing

end

end OAI
