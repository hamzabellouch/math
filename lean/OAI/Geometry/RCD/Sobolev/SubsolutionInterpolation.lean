import OAI.Geometry.RCD.Sobolev.SubsolutionUnitMean
import OAI.Geometry.RCD.Metric.RescaledBallVolume
import OAI.Geometry.RCD.Sobolev.GeometricMeanBootstrap
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-! # Interpolation of local subsolution mean bounds -/

open Set Metric Filter MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

/-- Distributional subsolutions restrict to smaller test domains. -/
theorem IsWeakSubsolutionOn.mono (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {s t : Set X} {u : SobolevSpace μ hQ} {a : ℝ}
    (hu : IsWeakSubsolutionOn μ hQ t u a) (hst : s ⊆ t) :
    IsWeakSubsolutionOn μ hQ s u a := by
  intro φ hφ
  exact hu ⟨φ.val,dirichlet_mono μ hQ hst φ.property⟩ hφ

/-- Young's inequality in the square-root form used for interior interpolation. -/
theorem sqrt_interpolation {θ c C H : ℝ} (hθ : 0 < θ) (hc : 0 ≤ c)
    (hC : 0 ≤ C) (hH : 0 ≤ H) :
    c*Real.sqrt (C*H) ≤ θ*C+(c^2/θ)*H := by
  have he : c*Real.sqrt (C*H) = Real.sqrt ((θ*C)*((c^2/θ)*H)) := by
    rw [show (θ*C)*((c^2/θ)*H) = c^2*(C*H) by field_simp,
      Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc]
  rw [he]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hx : 0 ≤ θ*C := mul_nonneg hθ.le hC
    have hy : 0 ≤ (c^2/θ)*H := by positivity
    nlinarith [sq_nonneg (θ*C),sq_nonneg ((c^2/θ)*H),mul_nonneg hx hy]

variable [BorelSpace X]

/-- A bound on a smaller ball interpolates the local L² norm with the
L¹ mass on the fixed outer ball. -/
theorem NoncollapsedRCD.local_mean_interpolation {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {p q : X} {R r D C : ℝ}
    (hR : 0 < R) (hr : 0 < r) (_hD : 0 ≤ D) (hC : 0 ≤ C)
    (hsub : ball q r ⊆ ball p R)
    (hvol : (hausdorff n X).real (ball p R) ≤ D*(hausdorff n X).real (ball q r))
    (u : SobolevSpace (hausdorff n X) hX.quadratic)
    (hpos : ∀ᵐ y ∂(hausdorff n X).restrict (ball p R), 0 ≤ SobolevSpace.toLp _ _ u y)
    (hbound : ∀ᵐ y ∂(hausdorff n X).restrict (ball q r), SobolevSpace.toLp _ _ u y ≤ C) :
    harmonicTargetNorm hX q r u ≤ Real.sqrt (D*C*
      ((hausdorff n X).real (ball p R))⁻¹*
        ∫ y in ball p R, SobolevSpace.toLp (hausdorff n X) hX.quadratic u y ∂hausdorff n X) := by
  let μ := hausdorff n X
  let U := SobolevSpace.toLp μ hX.quadratic u
  have hfinR := (hX.finiteOnBounded (ball p R) isBounded_ball).ne
  have hfinr := (hX.finiteOnBounded (ball q r) isBounded_ball).ne
  have hVR : 0 < μ.real (ball p R) := ENNReal.toReal_pos (hX.fullSupport p R hR).ne' hfinR
  have hVr : 0 < μ.real (ball q r) := ENNReal.toReal_pos (hX.fullSupport q r hr).ne' hfinr
  let : IsFiniteMeasure (μ.restrict (ball p R)) := ⟨by simpa using hfinR.lt_top⟩
  have hi : IntegrableOn U (ball p R) μ :=
    ((Lp.memLp U).restrict (ball p R)).integrable (by norm_num)
  have hmass : 0 ≤ ∫ y in ball p R, U y ∂μ := integral_nonneg_of_ae hpos
  have hI : (∫ y in ball q r, U y^2 ∂μ) ≤ C*(∫ y in ball p R, U y ∂μ) := by
    calc
      _ ≤ ∫ y in ball q r, C*U y ∂μ := by
        apply integral_mono_ae (Lp.memLp U).integrable_sq.integrableOn ((hi.mono_set hsub).const_mul C)
        filter_upwards [hbound,ae_restrict_of_ae_restrict_of_subset hsub hpos] with y hb hp
        nlinarith
      _ = C*(∫ y in ball q r, U y ∂μ) := integral_const_mul _ _
      _ ≤ C*(∫ y in ball p R, U y ∂μ) := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hi hpos (Eventually.of_forall hsub)) hC
  have hratio : (μ.real (ball q r))⁻¹ ≤ D*(μ.real (ball p R))⁻¹ := by
    apply (le_div_iff₀ hVR).mpr
    change (μ.real (ball q r))⁻¹*μ.real (ball p R) ≤ D
    exact (inv_mul_le_iff₀ hVr).mpr (by simpa only [mul_comm] using hvol)
  have hn : (harmonicTargetNorm hX q r u)^2 =
      (μ.real (ball q r))⁻¹*(∫ y in ball q r, U y^2 ∂μ) :=
    normalized_sobolev_mean_sq μ hX.quadratic _ hfinr u
  apply Real.le_sqrt_of_sq_le
  rw [hn]
  calc
    _ ≤ (μ.real (ball q r))⁻¹*(C*(∫ y in ball p R, U y ∂μ)) :=
      mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hVr.le)
    _ ≤ (D*(μ.real (ball p R))⁻¹)*(C*(∫ y in ball p R, U y ∂μ)) :=
      mul_le_mul_of_nonneg_right hratio (mul_nonneg hC hmass)
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
