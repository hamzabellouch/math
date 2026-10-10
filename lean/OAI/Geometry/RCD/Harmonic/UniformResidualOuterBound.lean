import OAI.Geometry.RCD.Transport.ScaledRadialTransportForcing
import OAI.Geometry.RCD.Transport.ScaledTransportConstants
import OAI.Geometry.RCD.Harmonic.ResidualOuterBound

namespace OAI

/-! # Uniform outer residual control on shrinking physical balls -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

/-- The transport constant is independent of the physical radius. The
radial pairing error has its natural length factor before normalization. -/
theorem uniform_residual_outer_bound (n : ℕ) {F E : ℝ} (hF : 0 ≤ F)
    (C : ℝ≥0) :
    ∃ T : ℝ, 0 ≤ T ∧ ∀ (R a : ℝ), 0 < R → 0 ≤ a → a ≤ (n : ℝ) + 1 →
      ∀ (z : X) (f w q : SobolevSpace μ hQ) (σ : ℝ), 0 ≤ σ →
      IsConstantLaplacianOn μ hQ (ball z (4 * R)) f a →
      ∀ {B : ℝ} (hf : ∀ᵐ x ∂μ.restrict (ball z (4 * R)), localGamma μ hQ f f x ≤ B),
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C) →
      ∀ e : X → ℝ, MemLp e 2 μ →
      localRadialDerivative μ hQ (ball z (4 * R)) f hf w =
        SobolevSpace.restrictLp μ hQ (ball z (4 * R)) (w + q) →
      localGamma μ hQ f (inwardSobolev μ hQ z (3 * R)) =ᵐ[μ.restrict (ball z (3 * R))]
        (fun x => e x - dist z x) →
      μ (sphere z R) = 0 →
      ‖SobolevSpace.restrictLp μ hQ (ball z (4 * R)) q‖ ≤
        F * (‖SobolevSpace.restrictLp μ hQ (ball z R) w‖ + σ) →
      (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) ≤ E ^ 2 * R ^ 2 * σ ^ 2 →
      ‖SobolevSpace.restrictLp μ hQ (ball z (2 * R)) w‖ ≤
        T * (‖SobolevSpace.restrictLp μ hQ (ball z R) w‖ + σ) := by
  let β := transportCutoffExponent n
  let q₀ := (2 : ℝ) ^ (β + 2)
  let d := q₀ / β
  have hβ : 0 < β := transportCutoffExponent_pos n
  have hq₀ : 0 ≤ q₀ := by dsimp only [q₀]; positivity
  have hd : 0 ≤ d := div_nonneg hq₀ hβ.le
  let A₀ := 1 + 2 * ((n : ℝ) + 3 + 1 / 4) * d
  let B₀ := 8 * d
  let C₀ := 4 * (C : ℝ) ^ 2 * q₀
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  have hB₀ : 0 ≤ B₀ := by dsimp only [B₀]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  let T := Real.sqrt (A₀ + B₀ * F ^ 2 + C₀ * E ^ 2)
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hTsq : T ^ 2 = A₀ + B₀ * F ^ 2 + C₀ * E ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨T, hT, ?_⟩
  intro R a hR ha han z f w q σ hσ hlap B hf hw e he heuler hradial hsphere hq herr
  let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
  let Q := R ^ (-(β + 1))
  let m := (R / 2) * (2 * R) ^ (-(β + 1))
  obtain ⟨hm, hD, hDm, hQm⟩ := scaled_transport_constants (n := n) hR
  change 0 < m at hm
  change 0 ≤ D at hD
  change D / m ≤ d at hDm
  change Q / (R * m) * R ^ 2 = q₀ at hQm
  have hDm0 : 0 ≤ D / m := div_nonneg hD hm.le
  have hQnonneg : 0 ≤ Q := by dsimp only [Q]; positivity
  let α := ‖SobolevSpace.restrictLp μ hQ (ball z R) w‖
  have hα : 0 ≤ α := norm_nonneg _
  have hαsum : α ^ 2 ≤ (α + σ) ^ 2 := by nlinarith
  have hσsum : σ ^ 2 ≤ (α + σ) ^ 2 := by nlinarith
  have hq2 : (∫ x in ball z (4 * R), (SobolevSpace.toLp μ hQ q x) ^ 2 ∂μ) ≤
      F ^ 2 * (α + σ) ^ 2 := by
    rw [← restrictLp_norm_sq μ hQ]
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hF (add_nonneg hα hσ))).mpr hq
  have hA : 1 + 2 * ((a + 2) * D + D / 4) / m ≤ A₀ := by
    calc
      _ = 1 + 2 * (a + 2 + 1 / 4) * (D / m) := by ring
      _ ≤ 1 + 2 * ((n : ℝ) + 3 + 1 / 4) * d := by
        exact add_le_add_right
          (mul_le_mul (by linarith) hDm hDm0 (by positivity)) 1
  have hB : 8 * D / m ≤ B₀ := by
    dsimp only [B₀]
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hDm (by norm_num : (0 : ℝ) ≤ 8)
  have hCE : (4 * (C : ℝ) ^ 2 * Q / (R * m)) *
      (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) ≤ C₀ * E ^ 2 * (α + σ) ^ 2 := by
    calc
      _ ≤ (4 * (C : ℝ) ^ 2 * Q / (R * m)) * (E ^ 2 * R ^ 2 * σ ^ 2) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ = 4 * (C : ℝ) ^ 2 * (Q / (R * m) * R ^ 2) * E ^ 2 * σ ^ 2 := by ring
      _ = C₀ * E ^ 2 * σ ^ 2 := by rw [hQm]
      _ ≤ C₀ * E ^ 2 * (α + σ) ^ 2 := mul_le_mul_of_nonneg_left hσsum (by positivity)
  have htrans := scaled_radial_transport_sobolev_forcing μ hQ hR ha han z f w q
    hlap hf C hw e he heuler hradial hsphere
  change (∫ x in ball z (2 * R), (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) ≤
    (1 + 2 * ((a + 2) * D + D / 4) / m) *
      (∫ x in ball z R, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) +
      (8 * D / m) * (∫ x in ball z (4 * R), (SobolevSpace.toLp μ hQ q x) ^ 2 ∂μ) +
      (4 * (C : ℝ) ^ 2 * Q / (R * m)) * (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) at htrans
  rw [← restrictLp_norm_sq μ hQ (ball z R) w, ← restrictLp_norm_sq μ hQ (ball z (2 * R)) w] at htrans
  have hfirst : (1 + 2 * ((a + 2) * D + D / 4) / m) * α ^ 2 ≤ A₀ * (α + σ) ^ 2 :=
    (mul_le_mul_of_nonneg_right hA (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hαsum hA₀)
  have hsecond : (8 * D / m) * (∫ x in ball z (4 * R), (SobolevSpace.toLp μ hQ q x) ^ 2 ∂μ) ≤
      B₀ * F ^ 2 * (α + σ) ^ 2 := by
    calc
      _ ≤ (8 * D / m) * (F ^ 2 * (α + σ) ^ 2) :=
        mul_le_mul_of_nonneg_left hq2 (by positivity)
      _ ≤ B₀ * (F ^ 2 * (α + σ) ^ 2) := mul_le_mul_of_nonneg_right hB (by positivity)
      _ = _ := by ring
  have hfinal : ‖SobolevSpace.restrictLp μ hQ (ball z (2 * R)) w‖ ^ 2 ≤
      (T * (α + σ)) ^ 2 := by
    calc
      _ ≤ _ := htrans.trans (add_le_add (add_le_add hfirst hsecond) hCE)
      _ = _ := by rw [mul_pow, hTsq]; ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hT (add_nonneg hα hσ))).mp hfinal

end RegularPointCoordinates

end

end OAI
