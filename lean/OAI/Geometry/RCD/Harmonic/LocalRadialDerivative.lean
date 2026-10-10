import OAI.Geometry.RCD.Coordinates.RadialFitCoordinates
import OAI.Geometry.RCD.Metric.InwardLocality

namespace OAI

/-! # The bounded radial derivative as a linear map into local L2 -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A locally bounded gradient defines a genuine linear derivative on
Sobolev functions with values in the common local L2 space. -/
def localRadialDerivative (Ω : Set X) (f : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B) :
    SobolevSpace μ hQ →ₗ[ℝ] Lp ℝ 2 (μ.restrict Ω) where
  toFun q := radialPairingLp μ hQ Ω q f hf
  map_add' q r := by
    apply Lp.ext
    filter_upwards [radialPairingLp_representative μ hQ Ω (q + r) f hf,
      radialPairingLp_representative μ hQ Ω q f hf,
      radialPairingLp_representative μ hQ Ω r f hf,
      Lp.coeFn_add (radialPairingLp μ hQ Ω q f hf) (radialPairingLp μ hQ Ω r f hf),
      ae_restrict_of_ae (localGamma_add_left μ hQ q r f)] with x hsum hq hr hadd hg
    simp only [hsum, hadd, Pi.add_apply, hq, hr, hg]
  map_smul' c q := by
    apply Lp.ext
    filter_upwards [radialPairingLp_representative μ hQ Ω (c • q) f hf,
      radialPairingLp_representative μ hQ Ω q f hf,
      Lp.coeFn_smul c (radialPairingLp μ hQ Ω q f hf),
      ae_restrict_of_ae (localGamma_smul_left μ hQ c q f)] with x hprod hq hsmul hg
    simp only [hprod, hsmul, Pi.smul_apply, smul_eq_mul, hq, hg, RingHom.id_apply]

/-- The map is the original radial gradient pairing, with its slots in
the customary order. -/
theorem localRadialDerivative_representative (Ω : Set X) (f q : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B) :
    localRadialDerivative μ hQ Ω f hf q =ᵐ[μ.restrict Ω] localGamma μ hQ f q :=
  (radialPairingLp_representative μ hQ Ω q f hf).trans
    (ae_restrict_of_ae (localGamma_comm μ hQ q f))

/-- This bound retains the local energy, so applying the derivative does
not discard the scale of an already constructed radial residual. -/
theorem localRadialDerivative_norm_sq (Ω : Set X) (f q : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B) :
    ‖localRadialDerivative μ hQ Ω f hf q‖ ^ 2 ≤
      B * ∫ x in Ω, localGamma μ hQ q q x ∂μ := by
  have hrep := localRadialDerivative_representative μ hQ Ω f q hf
  have heq : (fun x => (localRadialDerivative μ hQ Ω f hf q x) ^ 2)
      =ᵐ[μ.restrict Ω] fun x => (localGamma μ hQ f q x) ^ 2 := by
    filter_upwards [hrep] with x hx
    rw [hx]
  rw [l2_norm_sq_eq_integral, integral_congr_ae heq, ← integral_const_mul]
  apply integral_mono_ae
    ((localGamma_memLp_two_of_bound μ hQ Ω q f hf).integrable_sq.congr
      (by filter_upwards [ae_restrict_of_ae (localGamma_comm μ hQ q f)] with x hx; rw [hx]))
    ((localGamma_memL1 μ hQ q q).integrableOn.const_mul B)
  filter_upwards [hf, ae_restrict_of_ae (localGamma_sq_le μ hQ f q),
    ae_restrict_of_ae (localGamma_self μ hQ q)] with x hbound hsq hself
  apply hsq.trans
  exact mul_le_mul_of_nonneg_right hbound (by rw [hself]; positivity)

/-- Every local Sobolev representative of a radial pairing is its image
under this map. -/
theorem localRadialDerivative_eq_restrict (Ω : Set X) (f q g : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hg : SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict Ω] localGamma μ hQ f q) :
    localRadialDerivative μ hQ Ω f hf q = SobolevSpace.restrictLp μ hQ Ω g := by
  apply Lp.ext
  exact (localRadialDerivative_representative μ hQ Ω f q hf).trans
    (hg.symm.trans (SobolevSpace.restrictLp_coe μ hQ Ω g).symm)

/-- Constants in a local affine fit have zero radial derivative. -/
theorem localRadialDerivative_eq_of_constant_difference (Ω : Set X)
    (f q r : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B) (c : ℝ)
    (hqr : SobolevSpace.toLp μ hQ (q - r) =ᵐ[μ.restrict Ω] fun _ => c) :
    localRadialDerivative μ hQ Ω f hf q = localRadialDerivative μ hQ Ω f hf r := by
  exact radialPairingLp_congr μ hQ Ω q f r f hf hf
    (localGamma_eq_of_constant_difference μ hQ Ω q r f c hqr)

end RegularPointCoordinates

end

end OAI
