import OAI.Geometry.RCD.Harmonic.AffineCenterBounds
import OAI.Geometry.RCD.Sobolev.LocalAffineCutoff
import OAI.Geometry.RCD.Coordinates.CovectorConstantRecovery

namespace OAI

/-! # From recovered affine coefficients to the constant direction -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The two-center radial derivative is close to the actual displacement
once its affine linear and constant coefficients have been recovered. -/
theorem normalized_constant_direction_error {n : ℕ}
    (Ω : Set X) (hfin : μ Ω ≠ ∞) (hpos : μ Ω ≠ 0) (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (U H : Euclidean n →L[ℝ] SobolevSpace μ hQ) (B : Euclidean n →L[ℝ] Euclidean n)
    (c d : Euclidean n →L[ℝ] ℝ) {e R L D : ℝ} (hR : 0 ≤ R)
    (hU : ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (U b))‖ ≤ R * ‖b‖)
    (hfit : ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (H b - U (B b) - c b • η))‖ ≤ e * ‖b‖)
    (hB : ‖B‖ ≤ L) (hconst : ‖c - d‖ ≤ D) (b : Euclidean n) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (H b - d b • η))‖ ≤
      (e + R * L + D) * ‖b‖ := by
  have hlin : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (U (B b)))‖ ≤
      R * L * ‖b‖ := by
    apply (hU (B b)).trans
    have hb := (B.le_opNorm b).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg b))
    exact (mul_le_mul_of_nonneg_left hb hR).trans_eq (by ring)
  have hc : ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω ((c - d) b • η))‖ ≤
      D * ‖b‖ := by
    rw [map_smul, restrictLp_eq_one_of_representative μ hQ η Ω hfin hη,
      normalized_constant_norm μ Ω hfin hpos]
    change ‖(c - d) b‖ ≤ _
    exact ((c - d).le_opNorm b).trans (mul_le_mul_of_nonneg_right hconst (norm_nonneg b))
  have he : H b - d b • η =
      (H b - U (B b) - c b • η) + U (B b) + (c - d) b • η := by
    simp only [sub_apply, sub_smul]
    module
  rw [he, map_add, map_add]
  simp only [normalizeLocalL2, smul_add]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  have hf := hfit b
  dsimp only [normalizeLocalL2] at hf hlin hc
  nlinarith only [hf, hlin, hc]

/-- In the two-center application the affine constant is the displaced
coordinate covector composed with the first radial matrix. Both recovered
coefficient estimates therefore give the desired constant direction. -/
theorem normalized_two_center_direction_error {n : ℕ}
    (Ω : Set X) (hfin : μ Ω ≠ ∞) (hpos : μ Ω ≠ 0) (η : SobolevSpace μ hQ)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (U H : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (Ax Az : Euclidean n →L[ℝ] Euclidean n) (c d : Euclidean n →L[ℝ] ℝ)
    {e R L D M : ℝ} (hR : 0 ≤ R) (hx : ‖Ax - 1‖ ≤ 1 / 2) (hc : c = d.comp Ax)
    (hU : ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (U b))‖ ≤ R * ‖b‖)
    (hfit : ∀ b, ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω
      (H b - U ((Az - Ax) b) - c b • η))‖ ≤ e * ‖b‖)
    (hB : ‖Az - Ax‖ ≤ L) (hM : ‖c‖ ≤ M) (hconst : ‖c.comp (Az - 1)‖ ≤ D)
    (b : Euclidean n) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω (H b - d b • η))‖ ≤
      (e + R * L + 2 * (D + M * L)) * ‖b‖ := by
  exact normalized_constant_direction_error μ hQ Ω hfin hpos η hη U H (Az - Ax) c d hR hU hfit
    hB (covector_constant_recovery Ax Az d c hx hc hB hM hconst) b

end RegularPointCoordinates

end

end OAI
