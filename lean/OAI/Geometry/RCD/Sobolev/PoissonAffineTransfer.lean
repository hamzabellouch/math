import OAI.Geometry.RCD.Coordinates.RadialFitCoordinates
import OAI.Geometry.RCD.Sobolev.CorrectionInteriorEnergy

namespace OAI

/-! # Transfer the distance affine fit to the Poisson radial derivative -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The canonical Hessian pairing is the Poisson radial derivative.
Replacing the true distance by its Poisson solution costs only the
already proved Poisson energy error, times the coordinate gradient bound. -/
theorem LocalHessianPairing.fit_value_transfer {Ω : Set X}
    {f a : SobolevSpace μ hQ} (G : LocalHessianPairing μ hQ Ω f a)
    (q F : SobolevSpace μ hQ) {B error E : ℝ} (hB : 0 ≤ B)
    (ha : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ a a x ≤ B)
    (hpoisson : (∫ x in Ω, localGamma μ hQ (q - f) (q - f) x ∂μ) ≤ error)
    (hfit : ‖radialPairingLp μ hQ Ω q a ha - SobolevSpace.restrictLp μ hQ Ω F‖ ^ 2 ≤ E) :
    ‖SobolevSpace.restrictLp μ hQ Ω (G.mixed - F)‖ ^ 2 ≤ 2 * E + 2 * B * error := by
  let t := radialPairingLp μ hQ Ω q a ha
  let g := SobolevSpace.restrictLp μ hQ Ω G.mixed
  let u := SobolevSpace.restrictLp μ hQ Ω F
  have hdiff : ‖t - g‖ ^ 2 ≤ B * error := by
    rw [l2_norm_sq_eq_integral]
    have he : (fun x => ((t - g) x) ^ 2) =ᵐ[μ.restrict Ω]
        fun x => (localGamma μ hQ q a x - localGamma μ hQ f a x) ^ 2 := by
      filter_upwards [Lp.coeFn_sub t g, radialPairingLp_representative μ hQ Ω q a ha,
        SobolevSpace.restrictLp_coe μ hQ Ω G.mixed, G.mixed_rep] with x hs ht hg hx
      simp only [hs, Pi.sub_apply]
      change ((radialPairingLp μ hQ Ω q a ha) x -
        (SobolevSpace.restrictLp μ hQ Ω G.mixed) x) ^ 2 = _
      rw [ht, hg, hx]
    rw [integral_congr_ae he]
    exact (radial_pairing_error_le μ hQ Ω q f a ha).trans
      (mul_le_mul_of_nonneg_left hpoisson hB)
  have heq : g - u = (t - u) - (t - g) := by abel
  have hn := norm_sub_le (t - u) (t - g)
  have hn2 := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  change ‖t - u‖ ^ 2 ≤ E at hfit
  rw [map_sub]
  change ‖g - u‖ ^ 2 ≤ _
  rw [heq]
  nlinarith [sq_nonneg (‖t - u‖ - ‖t - g‖)]

end RegularPointCoordinates

end

end OAI
