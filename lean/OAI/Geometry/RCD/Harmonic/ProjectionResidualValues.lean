import OAI.Geometry.RCD.Harmonic.ColumnRepresentatives
import OAI.Geometry.RCD.Harmonic.RescaledRadialFunction

namespace OAI

/-! # Uniform values of the normalized actual projection residual -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
/-- Centered coordinate values bound every coefficient direction in its
own exact normalization frame. -/
theorem framed_coordinate_value_bound {n : ℕ} (Ω : Set X)
    (u : Fin n → SobolevSpace μ hQ) (V : X → Euclidean n)
    (N : Euclidean n ≃L[ℝ] Euclidean n) {r L : ℝ}
    (hrep : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[μ.restrict Ω] fun x => V x j)
    (hvalue : ∀ᵐ x ∂μ.restrict Ω,
      ‖(N : Euclidean n →L[ℝ] Euclidean n).adjoint (V x)‖ ≤ L * r)
    (b : Euclidean n) :
    ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u (N b)) x| ≤
      L * r * ‖b‖ := by
  filter_upwards [sobolevColumnMap_representative μ hQ u Ω V hrep (N b), hvalue]
    with x hr hv
  rw [hr]
  have hpair := ContinuousLinearMap.adjoint_inner_left
    (N : Euclidean n →L[ℝ] Euclidean n) b (V x)
  change ⟪(N : Euclidean n →L[ℝ] Euclidean n).adjoint (V x), b⟫_ℝ = ⟪V x, N b⟫_ℝ at hpair
  rw [← hpair]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))

omit [BorelSpace X] [ProperSpace X] in
/-- Both the constant and the linear part of the actual affine fit have
size `r²`; hence the normalized residual is uniformly bounded. -/
theorem physical_projection_residual_bound {n : ℕ} (Ω : Set X)
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (v η : SobolevSpace μ hQ) (c : ℝ) (b : Euclidean n)
    {r V H L : ℝ} (hr : 0 < r) (_hH : 0 ≤ H) (_hV : 0 ≤ V) (hL : 0 ≤ L)
    (hv : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ v x| ≤ V * r ^ 2)
    (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict Ω] fun _ => (1 : ℝ))
    (hu : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u (N b)) x| ≤
      L * r * ‖b‖)
    (hcoeff : |c| + r * ‖b‖ ≤ H * V * r ^ 2) :
    ∀ᵐ x ∂μ.restrict Ω,
      |SobolevSpace.toLp μ hQ ((r ^ 2)⁻¹ • (v - c • η - sobolevColumnMap μ hQ u (N b))) x| ≤
        V + (1 + L) * H * V := by
  have hc : |c| ≤ H * V * r ^ 2 := by nlinarith [mul_nonneg hr.le (norm_nonneg b)]
  have hb : r * ‖b‖ ≤ H * V * r ^ 2 := (le_add_of_nonneg_left (abs_nonneg c)).trans hcoeff
  apply rescaled_radial_value μ hQ Ω _ hr
  filter_upwards [hv, hη, hu,
    ae_restrict_of_ae (Lp.coeFn_sub
      (SobolevSpace.toLp μ hQ (v - c • η))
      (SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u (N b)))),
    ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ v)
      (SobolevSpace.toLp μ hQ (c • η))),
    ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp μ hQ η))] with x hv hη hu hs ht hm
  rw [map_sub, hs, Pi.sub_apply, map_sub, ht, Pi.sub_apply, map_smul, hm, Pi.smul_apply,
    smul_eq_mul, hη, mul_one]
  have hh := (abs_sub (SobolevSpace.toLp μ hQ v x - c)
    (SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u (N b)) x)).trans
      (add_le_add (abs_sub (SobolevSpace.toLp μ hQ v x) c) le_rfl)
  have hterm := mul_le_mul_of_nonneg_left hb hL
  calc
    _ ≤ (|SobolevSpace.toLp μ hQ v x| + |c|) +
        |SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u (N b)) x| := hh
    _ ≤ (V * r ^ 2 + H * V * r ^ 2) + L * (H * V * r ^ 2) := by
      nlinarith only [hv, hc, hu, hterm]
    _ = (V + (1 + L) * H * V) * r ^ 2 := by ring

end RegularPointCoordinates

end

end OAI
