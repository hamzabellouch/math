import OAI.Geometry.RCD.Transport.RadialTransportForcing
import OAI.Geometry.RCD.Harmonic.AffineForcingBound

namespace OAI

/-! # A uniform outer norm for an unnormalized projected residual -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
theorem restrictLp_norm_sq (Ω : Set X) (w : SobolevSpace μ hQ) :
    ‖SobolevSpace.restrictLp μ hQ Ω w‖ ^ 2 =
      ∫ x in Ω, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ := by
  rw [l2_norm_sq_eq_integral]
  exact integral_congr_ae ((SobolevSpace.restrictLp_coe μ hQ Ω w).pow_const 2)

/-- The larger-ball bound has a constant independent of both the small
inner residual norm and the source error. This is the estimate needed
before dividing the residual by its norm in the compactness argument. -/
theorem residual_outer_bound {n : ℕ} {R a F E : ℝ} (hR : 2 ≤ R)
    (ha : 0 ≤ a) (han : a ≤ (n : ℝ) + 1) (hF : 0 ≤ F)
    (C : ℝ≥0) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (z : X) (f w q : SobolevSpace μ hQ) (σ : ℝ), 0 ≤ σ →
      IsConstantLaplacianOn μ hQ (ball z (4 * R)) f a →
      ∀ {B : ℝ} (hf : ∀ᵐ x ∂μ.restrict (ball z (4 * R)), localGamma μ hQ f f x ≤ B),
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C) →
      ∀ e : X → ℝ, MemLp e 2 μ →
      localRadialDerivative μ hQ (ball z (4 * R)) f hf w =
        SobolevSpace.restrictLp μ hQ (ball z (4 * R)) (w + q) →
      localGamma μ hQ f (inwardSobolev μ hQ z (3 * R)) =ᵐ[μ.restrict (ball z (4 * R))]
        (fun x => e x - dist z x) →
      μ (sphere z R) = 0 →
      ‖SobolevSpace.restrictLp μ hQ (ball z (4 * R)) q‖ ≤
        F * (‖SobolevSpace.restrictLp μ hQ (ball z R) w‖ + σ) →
      (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) ≤ E ^ 2 * σ ^ 2 →
      ‖SobolevSpace.restrictLp μ hQ (ball z (2 * R)) w‖ ≤
        T * (‖SobolevSpace.restrictLp μ hQ (ball z R) w‖ + σ) := by
  let β := transportCutoffExponent n
  let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
  let Q := R ^ (-(β + 1))
  let m := ((2 * R) ^ (-β) - (3 * R) ^ (-β)) / β
  have hβ : 0 < β := transportCutoffExponent_pos n
  have hR0 : 0 < R := by linarith
  have hD : 0 ≤ D := le_of_lt (div_pos (sub_pos.mpr
    (Real.rpow_lt_rpow_of_neg hR0 (by linarith : R < 3 * R) (neg_neg_of_pos hβ))) hβ)
  have hQpos : 0 ≤ Q := Real.rpow_nonneg hR0.le _
  have hm : 0 < m := div_pos (sub_pos.mpr
    (Real.rpow_lt_rpow_of_neg (by positivity : 0 < 2 * R)
      (by linarith : 2 * R < 3 * R) (neg_neg_of_pos hβ))) hβ
  let A₀ := 1 + 2 * ((a + 2) * D + D / 4) / m
  let B₀ := 8 * D / m
  let C₀ := 2 * (C : ℝ) ^ 2 * Q / m
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  let T := Real.sqrt (A₀ + B₀ * F ^ 2 + C₀ * E ^ 2)
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hTsq : T ^ 2 = A₀ + B₀ * F ^ 2 + C₀ * E ^ 2 :=
    Real.sq_sqrt (by positivity)
  refine ⟨T, hT, ?_⟩
  intro z f w q σ hσ hlap B hf hw e he heuler hradial hsphere hq herr
  let α := ‖SobolevSpace.restrictLp μ hQ (ball z R) w‖
  have hα : 0 ≤ α := norm_nonneg _
  have hαsum : α ^ 2 ≤ (α + σ) ^ 2 := by nlinarith
  have hσsum : σ ^ 2 ≤ (α + σ) ^ 2 := by nlinarith
  have hq2 : (∫ x in ball z (4 * R), (SobolevSpace.toLp μ hQ q x) ^ 2 ∂μ) ≤
      F ^ 2 * (α + σ) ^ 2 := by
    rw [← restrictLp_norm_sq μ hQ]
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hF (add_nonneg hα hσ))).mpr hq
  have htrans := radial_transport_sobolev_forcing μ hQ hR ha han z f w q hlap hf C hw e he
    heuler hradial hsphere
  change (∫ x in ball z (2 * R), (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) ≤
    A₀ * (∫ x in ball z R, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) +
      B₀ * (∫ x in ball z (4 * R), (SobolevSpace.toLp μ hQ q x) ^ 2 ∂μ) +
        C₀ * (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) at htrans
  rw [← restrictLp_norm_sq μ hQ (ball z R) w] at htrans
  have hbound := htrans.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hαsum hA₀) (mul_le_mul_of_nonneg_left hq2 hB₀))
    (mul_le_mul_of_nonneg_left (herr.trans (mul_le_mul_of_nonneg_left hσsum (sq_nonneg E))) hC₀))
  rw [← restrictLp_norm_sq μ hQ (ball z (2 * R)) w] at hbound
  have hfinal : ‖SobolevSpace.restrictLp μ hQ (ball z (2 * R)) w‖ ^ 2 ≤
      (T * (α + σ)) ^ 2 := by
    calc
      _ ≤ _ := hbound
      _ = _ := by rw [mul_pow, hTsq]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (add_nonneg hα hσ))).mp hfinal

end RegularPointCoordinates

end

end OAI
