import OAI.Geometry.RCD.Coordinates.GramNormalization
import OAI.Geometry.RCD.Coordinates.PositiveForms

namespace OAI

/-! # Averaging gradients against normalized Sobolev coordinates -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  (U : E →L[ℝ] SobolevSpace μ hQ) (s : Set X) (hs : MeasurableSet s)

/-- The vector of mean gradient pairings with the coordinate columns.
It is defined using the canonical Sobolev Gram, not chosen coefficients. -/
def meanGradientVector : SobolevSpace μ hQ →L[ℝ] E :=
  U.adjoint.comp
    (sobolevMeanGram μ hQ (ContinuousLinearMap.id ℝ (SobolevSpace μ hQ)) s hs)

theorem meanGradientVector_inner (f : SobolevSpace μ hQ) (v : E) :
    ⟪meanGradientVector μ hQ U s hs f, v⟫_ℝ =
      (μ.real s)⁻¹ * ∫ x in s, localGamma μ hQ f (U v) x ∂μ := by
  simp only [meanGradientVector, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, sobolevMeanGram_inner,
    ContinuousLinearMap.id_apply]

theorem meanGradientVector_column (v : E) :
    meanGradientVector μ hQ U s hs (U v) = sobolevMeanGram μ hQ U s hs v := by
  apply ext_inner_right ℝ
  intro z
  rw [meanGradientVector_inner, sobolevMeanGram_inner]

/-- Bessel's inequality for gradients in exactly normalized coordinates.
The right side is the actual averaged local Cheeger energy of `f`. -/
theorem meanGradientVector_norm_sq_le
    (hnormal : sobolevMeanGram μ hQ U s hs = ContinuousLinearMap.id ℝ E)
    (f : SobolevSpace μ hQ) :
    ‖meanGradientVector μ hQ U s hs f‖ ^ 2 ≤
      (μ.real s)⁻¹ * ∫ x in s, (SobolevSpace.minimalSlope μ hQ f x) ^ 2 ∂μ := by
  let S := sobolevMeanGram μ hQ
    (ContinuousLinearMap.id ℝ (SobolevSpace μ hQ)) s hs
  let v := meanGradientVector μ hQ U s hs f
  have hS := sobolevMeanGram_isPositive μ hQ
    (ContinuousLinearMap.id ℝ (SobolevSpace μ hQ)) s hs
  have hcross : ⟪f, S (U v)⟫_ℝ = ‖v‖ ^ 2 := by
    rw [← hS.inner_left_eq_inner_right, ← ContinuousLinearMap.adjoint_inner_left]
    change ⟪v, v⟫_ℝ = ‖v‖ ^ 2
    exact real_inner_self_eq_norm_sq v
  have hU : ⟪U v, S (U v)⟫_ℝ = ‖v‖ ^ 2 := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change ⟪v, meanGradientVector μ hQ U s hs (U v)⟫_ℝ = _
    rw [meanGradientVector_column, hnormal, ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
  have hcs := positive_form_cauchy_schwarz hS f (U v)
  rw [hcross, hU] at hcs
  have henergy : ⟪f, S f⟫_ℝ = (μ.real s)⁻¹ *
      ∫ x in s, (SobolevSpace.minimalSlope μ hQ f x) ^ 2 ∂μ := by
    exact sobolevMeanGram_energy μ hQ
      (ContinuousLinearMap.id ℝ (SobolevSpace μ hQ)) s hs f
  rw [henergy] at hcs
  change ‖v‖ ^ 2 ≤ _
  by_cases hv : v = 0
  · simp only [hv, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [← henergy]
    exact hS.inner_nonneg_right f
  have hvpos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  nlinarith

/-- Averaging the gradient of a fitted function recovers its linear
coefficient, with an error bounded by the residual energy. -/
theorem meanGradientVector_coefficient_error
    (hnormal : sobolevMeanGram μ hQ U s hs = ContinuousLinearMap.id ℝ E)
    (f : SobolevSpace μ hQ) (b : E) :
    ‖meanGradientVector μ hQ U s hs f - b‖ ^ 2 ≤
      (μ.real s)⁻¹ * ∫ x in s,
        (SobolevSpace.minimalSlope μ hQ (f - U b) x) ^ 2 ∂μ := by
  have h := meanGradientVector_norm_sq_le μ hQ U s hs hnormal (f - U b)
  rwa [map_sub, meanGradientVector_column, hnormal, ContinuousLinearMap.id_apply] at h

end RegularPointCoordinates

end

end OAI
