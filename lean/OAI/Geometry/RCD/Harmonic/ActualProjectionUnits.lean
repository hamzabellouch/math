import OAI.Geometry.RCD.Harmonic.ScaledProjectionData
import OAI.Geometry.RCD.Harmonic.RadialVolumeUnits
import OAI.Geometry.RCD.Harmonic.ForcingCoefficient

namespace OAI

/-! # The exact coefficient and forcing units of the actual projection -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- Passing from the radius-weighted physical covector to the coefficient
of the rescaled coordinates costs only the fixed radius ratio and frame norm. -/
theorem projection_coefficient_rescale {n : ℕ} (N : Euclidean n ≃L[ℝ] Euclidean n)
    {r M G alpha sigma : ℝ} (hr : 0 < r) (hN : ‖(N : Euclidean n →L[ℝ] Euclidean n)‖ ≤ M)
    (ell : Euclidean n) (k : ℝ)
    (hbound : |(r ^ 2)⁻¹ * k| + (r / 2048) * ‖N.symm ((r ^ 2)⁻¹ • ell)‖ ≤
      G * (alpha + sigma)) :
    ‖r⁻¹ • ell‖ + |(r ^ 2)⁻¹ * k| ≤
      max 1 (2048 * M) * G * (alpha + sigma) := by
  have hnorm : ‖(r ^ 2)⁻¹ • ell‖ ≤ M * ‖N.symm ((r ^ 2)⁻¹ • ell)‖ := by
    calc
      _ = ‖N (N.symm ((r ^ 2)⁻¹ • ell))‖ := by rw [N.apply_symm_apply]
      _ ≤ ‖(N : Euclidean n →L[ℝ] Euclidean n)‖ * ‖N.symm ((r ^ 2)⁻¹ • ell)‖ :=
        by
          change ‖(N : Euclidean n →L[ℝ] Euclidean n) (N.symm ((r ^ 2)⁻¹ • ell))‖ ≤ _
          exact (N : Euclidean n →L[ℝ] Euclidean n).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right hN (norm_nonneg _)
  have heq : r⁻¹ • ell = r • ((r ^ 2)⁻¹ • ell) := by
    rw [smul_smul]
    congr 1
    field_simp
  have hlin : ‖r⁻¹ • ell‖ ≤ (2048 * M) * ((r / 2048) * ‖N.symm ((r ^ 2)⁻¹ • ell)‖) := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith only [mul_le_mul_of_nonneg_left hnorm hr.le]
  have hweight : 0 ≤ (r / 2048) * ‖N.symm ((r ^ 2)⁻¹ • ell)‖ := by positivity
  have hterm := mul_le_mul_of_nonneg_right (le_max_right 1 (2048 * M)) hweight
  have hconst := mul_le_mul_of_nonneg_right (le_max_left 1 (2048 * M)) (abs_nonneg ((r ^ 2)⁻¹ * k))
  have htotal := mul_le_mul_of_nonneg_left hbound
    (le_trans zero_le_one (le_max_left 1 (2048 * M)))
  nlinarith only [hlin, hterm, hconst, htotal]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The rescaled Euler equation is exactly the finite-coordinate identity
used by the published compactness theorem, including its constant term. -/
theorem radius_scaled_projection_euler_sum {n : ℕ} {r B B' : ℝ} (hr : 0 < r)
    (Ω : Set X) (hfin : μ Ω ≠ ∞) (u : Fin n → SobolevSpace μ hQ)
    (f w eta e : SobolevSpace μ hQ) (ell : Euclidean n) (k : ℝ)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hf' : ∀ᵐ x ∂μ.restrict Ω,
      localGamma μ hQ ((r ^ 2)⁻¹ • f) ((r ^ 2)⁻¹ • f) x ≤ B')
    (hid : localRadialDerivative μ hQ Ω f hf w = SobolevSpace.restrictLp μ hQ Ω
      (w + sobolevColumnMap μ hQ u ell + k • eta + e)) :
    r ^ 2 • localRadialDerivative μ hQ Ω ((r ^ 2)⁻¹ • f) hf' ((r ^ 2)⁻¹ • w) =
      SobolevSpace.restrictLp μ hQ Ω ((r ^ 2)⁻¹ • w) +
      (∑ j, (r⁻¹ • ell) j • SobolevSpace.restrictLp μ hQ Ω (radiusScaledColumns μ hQ r u j)) +
      ((r ^ 2)⁻¹ * k) • restrictedOne μ Ω hfin +
      SobolevSpace.restrictLp μ hQ Ω ((r ^ 2)⁻¹ • e) := by
  rw [radius_scaled_projection_euler μ hQ hr Ω u f w eta e ell k hf hf' hid]
  simp only [map_add, map_smul, sobolevColumnMap_apply, map_sum,
    restrictLp_eq_one_of_representative μ hQ eta Ω hfin heta,
    Finset.smul_sum, smul_smul, PiLp.smul_apply, smul_eq_mul]

omit [BorelSpace X] [ProperSpace X] in
/-- A mean-square norm is unchanged when only the proof of finiteness or
the presentation of the same measurable set changes. -/
theorem normalized_sobolev_norm_congr {s t : Set X} (hst : s = t)
    (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) (w : SobolevSpace μ hQ) :
    ‖normalizeLocalL2 μ s hs (SobolevSpace.restrictLp μ hQ s w)‖ =
      ‖normalizeLocalL2 μ t ht (SobolevSpace.restrictLp μ hQ t w)‖ := by
  subst t
  rfl

end RegularPointCoordinates

end

end OAI
