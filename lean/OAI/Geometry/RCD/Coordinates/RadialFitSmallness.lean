import OAI.Geometry.RCD.Coordinates.RadialFitCoordinates
import OAI.Geometry.RCD.Coordinates.NormalizedRadialError

namespace OAI

/-! # Passing the actual radial approximation to its least-squares error -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Any actual linear coordinate approximation bounds the affine fit.
This transfers the proved radial L2 smallness to the dimensionless errors
used in the dyadic recurrence. -/
theorem radialFitError_sq_le_linear {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (p : X) (r : ℝ) (hfin : μ (Metric.ball p r) ≠ ∞)
    (q a : SobolevSpace μ hQ) {B E : ℝ}
    (ha : ∀ᵐ x ∂μ.restrict (Metric.ball p r), localGamma μ hQ a a x ≤ B)
    (b : Euclidean n)
    (herror : (∫ x in Metric.ball p r, (localGamma μ hQ q a x -
      SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u b) x) ^ 2 ∂μ) ≤ E) :
    (radialFitError μ hQ u p r hfin q a ha) ^ 2 ≤
      ((μ.real (Metric.ball p r))⁻¹ * E) / r ^ 2 := by
  let s := Metric.ball p r
  let f := radialPairingLp μ hQ s q a ha
  let g := SobolevSpace.restrictLp μ hQ s (sobolevColumnMap μ hQ u b)
  have hcand : affineCoordinateMap μ hQ u s hfin (0, b) = g := by
    simp only [affineCoordinateMap_apply, zero_smul, zero_add, g]
  have he : affineResidual μ hQ u s hfin (f - g) = affineResidual μ hQ u s hfin f := by
    rw [← hcand]
    exact affineResidual_sub_affine μ hQ u s hfin f 0 b
  have hn := normalized_affineResidual_norm_le μ hQ u s hfin (f - g)
  rw [he] at hn
  have hn2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
  have hfg : (fun x => ((f - g) x) ^ 2) =ᵐ[μ.restrict s]
      fun x => (localGamma μ hQ q a x - SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u b) x) ^ 2 := by
    filter_upwards [Lp.coeFn_sub f g, radialPairingLp_representative μ hQ s q a ha,
      SobolevSpace.restrictLp_coe μ hQ s (sobolevColumnMap μ hQ u b)] with x hs hf hg
    rw [hs, Pi.sub_apply, hf, hg]
  have hi : ‖normalizeLocalL2 μ s hfin (f - g)‖ ^ 2 ≤ (μ.real s)⁻¹ * E := by
    rw [normalizeLocalL2_norm_sq, integral_congr_ae hfg]
    exact mul_le_mul_of_nonneg_left herror (by positivity)
  have hsq := hn2.trans hi
  change (‖normalizeLocalL2 μ s hfin (affineResidual μ hQ u s hfin f)‖ / r) ^ 2 ≤ _
  rw [div_pow]
  exact div_le_div_of_nonneg_right hsq (sq_nonneg r)

end RegularPointCoordinates

end

end OAI
