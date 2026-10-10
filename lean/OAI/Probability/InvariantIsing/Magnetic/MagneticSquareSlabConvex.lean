import OAI.Probability.InvariantIsing.Magnetic.MagneticSquareInverseConvex

namespace OAI

/-! Nonnegative inverse-spin second derivatives of the actual finite-level
conditional square means, after an additional Gaussian root step. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticScalarSlabSquare_second_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (i : Fin (L.length + 1)) {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    {v s : ℝ} (hv : 0 ≤ v) (hs : |s| < 1) :
    0 ≤ magneticScalarSlabContinuationSecond L hL
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ v s := by
  have hinit : ∀ u, |u| < 1 → 0 ≤ magneticScalarSlabWeighted L hL
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ 0 u := by
    intro u hu
    rw [magneticScalarSlabWeighted_zero]
    exact magneticScalarSquare_inverse_convex L hL hL1 i _
  have hn := magneticScalarSlabWeighted_nonneg L hL hL1 _
    (magneticScalarSquareFourJet_sandwich L hL i) hζ hζ1 hinit hv hs
  rw [magneticScalarSlabWeighted_eq_curvature_square L hL _ hζ] at hn
  exact nonneg_of_mul_nonneg_right hn (sq_pos_of_pos
    (magneticScalarInverseCurvature_pos L hL hζ v s))

theorem magneticScalarSlabSquare_deriv2_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (i : Fin (L.length + 1)) {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    {v s : ℝ} (hv : 0 ≤ v) (hs : |s| < 1) :
    0 ≤ deriv (deriv (magneticScalarSlabContinuation L
      (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ v)) s := by
  rw [magneticScalarSlabContinuation_second_deriv L hL _ hζ hs v]
  exact magneticScalarSlabSquare_second_nonneg L hL hL1 i hζ hζ1 hv hs

end InvariantIsing

end

end OAI
