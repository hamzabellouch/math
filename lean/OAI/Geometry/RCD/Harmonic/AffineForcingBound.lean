import OAI.Geometry.RCD.Harmonic.ForcingCoefficient

namespace OAI

/-! # The full forcing is controlled before residual normalization -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The exact-frame coefficient estimate controls the forcing on the
larger transport ball, including its constant and Sobolev error. -/
theorem affine_forcing_norm_bound {n : ℕ} (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (hpos : μ Ω ≠ 0) (η e : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (U : Euclidean n →L[ℝ] SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (ell : Euclidean n) (k : ℝ) {R C D α s : ℝ}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hα : 0 ≤ α)
    (hU : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (U ell))‖ ≤ R * ‖N.symm ell‖)
    (hcoeff : |k| + ‖N.symm ell‖ ≤ C * (α + s))
    (he : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω e)‖ ≤ D * s) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (U ell + k • η + e))‖ ≤
      ((1 + R) * C + D) * (α + s) := by
  have hconst : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (k • η))‖ = |k| := by
    rw [map_smul, restrictLp_eq_one_of_representative μ hQ η Ω hfin hη,
      normalized_constant_norm μ Ω hfin hpos]
  have hsum : R * ‖N.symm ell‖ + |k| ≤ (1 + R) * (|k| + ‖N.symm ell‖) := by
    nlinarith [abs_nonneg k, norm_nonneg (N.symm ell), mul_nonneg hR (abs_nonneg k)]
  have hb := hsum.trans (mul_le_mul_of_nonneg_left hcoeff (by positivity : 0 ≤ 1 + R))
  rw [map_add, map_add]
  simp only [normalizeLocalL2, smul_add] at hU he hconst ⊢
  apply le_trans ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))
  rw [hconst]
  have hh := add_le_add (add_le_add hU (le_rfl : |k| ≤ |k|)) he
  exact hh.trans (by nlinarith only [hb, mul_nonneg hD hα])

end RegularPointCoordinates

end

end OAI
