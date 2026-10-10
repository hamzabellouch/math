import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabCoefficient
import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabInitial

namespace OAI

/-! Closed-spin-interval derivatives of the finite slab. The two endpoints
are constant zero in time, while all spatial derivatives are used only
in the open spin interval. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def closedMagneticScalarSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  if |q.2| < 1 then magneticScalarInverseSlope L hL ζ q.1 q.2 else 0

def closedMagneticScalarSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  if |q.2| < 1 then magneticScalarInverseSecond L hL ζ q.1 q.2 else 0

def closedMagneticScalarTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ : ℝ) (q : ℝ × ℝ) : ℝ :=
  (closedMagneticScalarCurvature L hL ζ q) ^ 2 / 2 * closedMagneticScalarSecond L hL ζ q +
    ζ * (closedMagneticScalarCurvature L hL ζ q) ^ 2

lemma closedMagneticScalarCurvature_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticScalarCurvature L hL ζ (v, u))
      (closedMagneticScalarSlope L hL ζ (v, s)) s := by
  have he : (fun u => closedMagneticScalarCurvature L hL ζ (v, u)) =ᶠ[𝓝 s]
      magneticScalarInverseCurvature L hL ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticScalarSlope, hs, ite_true] using
    (magneticScalarInverseCurvature_hasDerivAt_spin L hL hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticScalarSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => closedMagneticScalarSlope L hL ζ (v, u))
      (closedMagneticScalarSecond L hL ζ (v, s)) s := by
  have he : (fun u => closedMagneticScalarSlope L hL ζ (v, u)) =ᶠ[𝓝 s]
      magneticScalarInverseSlope L hL ζ v := by
    filter_upwards [(isOpen_lt continuous_id.abs continuous_const).mem_nhds hs] with u hu
    exact ite_eq_left hu
  simpa only [closedMagneticScalarSecond, hs, ite_true] using
    (magneticScalarInverseSlope_hasDerivAt L hL hζ hs v).congr_of_eventuallyEq he

lemma closedMagneticScalarCurvature_hasDerivAt_time (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {ζ v : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (s : ℝ) :
    HasDerivAt (fun t => closedMagneticScalarCurvature L hL ζ (t, s))
      (closedMagneticScalarTime L hL ζ (v, s)) v := by
  by_cases hs : |s| < 1
  · have hd := magneticScalarInverseCurvature_PDE L hL hζ hs hv
    rw [magneticScalarInverse_second_deriv L hL hζ hs v] at hd
    simpa only [closedMagneticScalarCurvature, closedMagneticScalarSecond,
      closedMagneticScalarTime, hs, ite_true] using hd
  · simpa only [closedMagneticScalarCurvature, closedMagneticScalarSecond,
      closedMagneticScalarTime, hs, ite_false, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, zero_mul, mul_zero, add_zero] using (hasDerivAt_const v (0 : ℝ))

lemma closedMagneticScalarCurvature_endpoints (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ v : ℝ) :
    closedMagneticScalarCurvature L hL ζ (v, -1) = 0 ∧
      closedMagneticScalarCurvature L hL ζ (v, 1) = 0 := by
  simp only [closedMagneticScalarCurvature, abs_neg, abs_one, lt_self_iff_false, ite_false,
    and_self]

lemma closedMagneticScalarCurvature_le_one (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (q : ℝ × ℝ) (hq : q.2 ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ q ≤ 1 := by
  exact (closedMagneticScalarCurvature_le_spin_variance L hL hL1 hζ hζ1 q hq).trans
    (by linarith [sq_nonneg q.2])

lemma closedMagneticScalarCurvature_weighted_second_bound (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (q : ℝ × ℝ) :
    |closedMagneticScalarCurvature L hL ζ q * closedMagneticScalarSecond L hL ζ q| ≤
      magneticSlabPotentialCap L ζ := by
  by_cases hs : |q.2| < 1
  · simpa only [closedMagneticScalarCurvature, closedMagneticScalarSecond, hs, ite_true] using
      magneticScalarInverse_weighted_second_bound L hL hL1 hζ hζ1 q.1 q.2
  · simp only [closedMagneticScalarCurvature, closedMagneticScalarSecond, hs, ite_false,
      mul_zero, abs_zero]
    exact add_nonneg (magneticFourthRatioCap_nonneg _) (sq_nonneg _)

lemma closedMagneticScalarCurvature_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (ζ η s : ℝ) :
    closedMagneticScalarCurvature L hL ζ (0, s) =
      closedMagneticScalarCurvature L hL η (0, s) := by
  by_cases hs : |s| < 1
  · simp only [closedMagneticScalarCurvature, hs, ite_true, magneticScalarInverseCurvature_eq,
      Real.toNNReal_zero, fieldCurvatureTransform, fieldSpinTransition_zero_variance,
      sub_self, mul_zero, add_zero]
    rw [magneticScalarSlabBias_zero L ζ η s]
  · simp only [closedMagneticScalarCurvature, hs, ite_false]

end InvariantIsing

end

end OAI
