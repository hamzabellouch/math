import OAI.Geometry.RCD.Coordinates.NormalizedPoissonEulerGradient
import OAI.Geometry.RCD.Sobolev.EulerForcing
import OAI.Geometry.RCD.Coordinates.NormalizedPairing

namespace OAI

/-! # Scalar Euler forcing for the actual two-center replacements -/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Poincare constructs the scalar error from the actual full-mass
Euler-gradient estimate. The normalized squared error is linear in the
original two source defects, with one constant at every dyadic scale. -/
theorem actual_poisson_euler_forcing {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hhessian : LocalPoissonHessianActionInput hX)
    (hproduct : LocalPoissonGradientProductInput hX)
    (hpoincare : LocalMeanPoincareInput hX) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ Cp : ℝ, 1 ≤ Cp ∧ ∀
    {B J C A Cχ epsilon r0 : ℝ} (_hK : -κ ≤ K)
    (_hB : 0 ≤ B) (_hJ : 0 ≤ J) (_hCχ : 0 ≤ Cχ)
    (_hA : 0 ≤ A) (_hepsilon : 0 ≤ epsilon) (p₁ p₂ z : X)
    (S₁ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₁ r0)
    (S₂ : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p₂ r0)
    (T₁ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₁ B J C)
    (T₂ : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S₂ B J C)
    (i : ℕ)
    (_hroom₁ : dist z p₁ ≤ distanceSourceRadius r0 i / 4)
    (_hroom₂ : dist z p₂ ≤ distanceSourceRadius r0 i / 4)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (_hu : ∀ j, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
      (ball z (distanceSourceRadius r0 i / 4)) (u j))
    (_hgrad : ∀ j, ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ (1 + epsilon) ^ 2)
    (_hf₁ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₁.replacement i) (T₁.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (_hf₂ : ∀ᵐ x ∂(hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 4)),
      localGamma (hausdorff n X) hX.quadratic (T₂.replacement i) (T₂.replacement i) x ≤
        (A * distanceSourceRadius r0 i) ^ 2)
    (_χ : GoodLaplacianCutoff (hausdorff n X) hX.quadratic z (distanceSourceRadius r0 i / 64) Cχ)
    (_hcurv : -κ ≤ K * (distanceSourceRadius r0 i / 512) ^ 2)
    (η : SobolevSpace (hausdorff n X) hX.quadratic)
    (_hη : SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
      (hausdorff n X).restrict (ball z (distanceSourceRadius r0 i / 512))]
      fun _ => (1 : ℝ))
    (_hvolume : |(hausdorff n X).real (ball z (distanceSourceRadius r0 i / 64)) /
      (euclideanUnitVolume n * (distanceSourceRadius r0 i / 64) ^ n) - 1| ≤ 1 / 4)
    (_hvolumeSmall : |(hausdorff n X).real (ball z (distanceSourceRadius r0 i / 512)) /
      (euclideanUnitVolume n * (distanceSourceRadius r0 i / 512) ^ n) - 1| ≤ 1 / 4),
    ∃ (k : ℝ) (e : SobolevSpace (hausdorff n X) hX.quadratic),
      let μ := hausdorff n X
      let s := distanceSourceRadius r0 i
      let Ω := ball z (s / 512)
      let v := T₂.replacement i - T₁.replacement i
      (localGamma μ hX.quadratic (T₂.replacement i) v =ᵐ[μ.restrict Ω]
        fun x => SobolevSpace.toLp μ hX.quadratic v x + k +
          SobolevSpace.toLp μ hX.quadratic e x) ∧
      ‖normalizeLocalL2 μ Ω (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp μ hX.quadratic Ω ((s ^ 2)⁻¹ • e))‖ ^ 2 ≤
        (Cp / 512) ^ 2 * ((5 / 3 : ℝ) * (8 : ℝ) ^ n) *
          poissonEulerGradientConstant n A B J Cχ *
          (normalizedPoissonDefect μ hX.quadratic S₁ i +
            normalizedPoissonDefect μ hX.quadratic S₂ i) := by
  obtain ⟨Cp, hCp, hP⟩ := hpoincare.euler_forcing hκ
  refine ⟨Cp, hCp, ?_⟩
  intro B J C A Cχ epsilon r0 hK hB hJ hCχ hA hepsilon p₁ p₂ z S₁ S₂ T₁ T₂ i
    hroom₁ hroom₂ u hu hgrad hf₁ hf₂ χ hcurv η hη hvolume hvolumeSmall
  dsimp only
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let s := distanceSourceRadius r0 i
  let v := T₂.replacement i - T₁.replacement i
  let Ω := ball z (s / 512)
  let W := μ.real (ball z (s / 64))
  let W₀ := μ.real Ω
  let P := normalizedPoissonDefect μ hQ S₁ i + normalizedPoissonDefect μ hQ S₂ i
  let H := poissonEulerGradientConstant n A B J Cχ
  let D := (5 / 3 : ℝ) * (8 : ℝ) ^ n
  have hs : 0 < s := distanceSourceRadius_pos S₁.radius_pos i
  have hW : 0 < W := (quarter_volume_bounds (by positivity : 0 < s / 64)
    (euclideanUnitVolume_pos n) hvolume).1
  have hW₀ : 0 < W₀ := (quarter_volume_bounds (by positivity : 0 < s / 512)
    (euclideanUnitVolume_pos n) hvolumeSmall).1
  have hP0 : 0 ≤ P := add_nonneg (normalizedPoissonDefect_nonneg μ hQ S₁ hκ i)
    (normalizedPoissonDefect_nonneg μ hQ S₂ hκ i)
  have hH : 0 ≤ H := by
    have homega := euclideanUnitVolume_pos n
    dsimp only [H, poissonEulerGradientConstant]
    positivity
  have hratio : W ≤ D * W₀ := by
    have hh := radial_fraction_volume_ratio (by positivity : 0 < s / 64)
      (by norm_num : (0 : ℝ) < 1 / 8) (euclideanUnitVolume_pos n) hvolume
      (by convert hvolumeSmall using 1; congr 3; ring)
    have heq : ((1 / 8 : ℝ) ^ n)⁻¹ = (8 : ℝ) ^ n := by rw [← inv_pow]; norm_num
    rw [heq] at hh
    exact (div_le_iff₀ hW₀).mp hh
  obtain ⟨G, hG, henergy⟩ := normalized_poisson_euler_gradient hX hhessian hproduct
    hκ hK hB hJ hCχ hA hepsilon p₁ p₂ z S₁ S₂ T₁ T₂ i hroom₁ hroom₂
    u hu hgrad hf₁ hf₂ χ hvolume
  have hGsmall := ae_restrict_of_ae_restrict_of_subset
    (ball_subset_ball (by linarith : s / 512 ≤ s / 64)) hG
  obtain ⟨k, e, heuler, he⟩ := hP z (s / 512) (by positivity) hcurv
    (T₂.replacement i) v G η hGsmall hη
  refine ⟨k, e, heuler, ?_⟩
  have hraw : (∫ x in ball z (s / 64), localGamma μ hQ (G - v) (G - v) x ∂μ) ≤
      W * (H * s ^ 2 * P) := by
    have hd : (∫ x in ball z (s / 64), localGamma μ hQ (G - v) (G - v) x ∂μ) / W ≤
        H * s ^ 2 * P := by
      simpa only [W, s, μ, hQ, v, H, P, div_eq_mul_inv, mul_comm] using henergy
    simpa only [mul_comm] using (div_le_iff₀ hW).mp hd
  rw [show 8 * (s / 512) = s / 64 by ring] at he
  have he' : (∫ x in Ω, (SobolevSpace.toLp μ hQ e x) ^ 2 ∂μ) ≤
      (Cp * (s / 512)) ^ 2 * (D * W₀ * (H * s ^ 2 * P)) := by
    exact he.trans (mul_le_mul_of_nonneg_left (hraw.trans
      (mul_le_mul_of_nonneg_right hratio (by positivity))) (sq_nonneg _))
  rw [map_smul, normalizeLocalL2_smul, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_inv, abs_of_pos (sq_pos_of_pos hs), normalized_sobolev_mean_sq]
  calc
    _ ≤ ((s ^ 2)⁻¹) ^ 2 * (W₀⁻¹ *
        ((Cp * (s / 512)) ^ 2 * (D * W₀ * (H * s ^ 2 * P)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he' (inv_nonneg.mpr hW₀.le))
        (sq_nonneg _)
    _ = (Cp / 512) ^ 2 * D * H * P := by field_simp [hs.ne', hW₀.ne']

end RegularPointCoordinates

end

end OAI
