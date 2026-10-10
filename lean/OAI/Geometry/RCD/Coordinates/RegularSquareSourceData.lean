import OAI.Geometry.RCD.Coordinates.RegularBochnerSquare

namespace OAI

/-! # Bounded local Sobolev sources for actual squared regular directions -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

theorem regular_square_source_data [μ.Regular]
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hD : ∀ a, IsWeakLaplacian μ hQ (U a) (D a))
    (hH : ∀ a b, SobolevSpace.toLp μ hQ (H a b) =ᵐ[μ] localGamma μ hQ (U a) (U b))
    {Ω : Set X} (w z : Euclidean m) (G : X →ᵇ ℝ)
    (hG : SobolevSpace.toLp μ hQ (U w) =ᵐ[μ] G)
    (hz : U z=SobolevSpace.product μ hQ (U w) (U w) ‖G‖₊ ‖G‖₊)
    (d : SobolevSpace μ hQ) (A : ℝ≥0)
    (hd : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ d x|≤A)
    (hDr : D w =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ d) :
    ∃ dz : SobolevSpace μ hQ, ∃ B : ℝ≥0,
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dz x|≤B) ∧
      D z =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dz := by
  have hgb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (U w) x|≤‖G‖₊ := by
    filter_upwards [hG] with x hx
    rw [hx]
    exact G.norm_coe_le_norm x
  have hL : ∀ᵐ x ∂μ, localGamma μ hQ (U w) (U w) x≤(L w:ℝ)^2 := by
    filter_upwards [localGamma_self μ hQ (U w),hU w,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (U w))] with x he hb h0
    rw [he]
    exact pow_le_pow_left₀ h0 hb 2
  let dz := SobolevSpace.product μ hQ (U w) d ‖G‖₊ A+
    SobolevSpace.product μ hQ (U w) d ‖G‖₊ A+(2:ℝ) • H w w
  obtain ⟨q,hq,hqr⟩ := (hD w).square_local μ hQ (U w) (H w w) d (D w)
    ‖G‖₊ A (L w) hgb hd hL (ae_restrict_of_ae (hH w w)) hDr
  have hqz : D z=q := IsWeakLaplacian.unique μ hQ (by simpa only [hz] using hD z) hq
  refine ⟨dz,2*‖G‖₊*A+2*(L w*L w),?_,?_⟩
  · exact squareLaplacianSource_bound μ hQ (U w) (H w w) d ‖G‖₊ A (L w*L w)
      hgb hd (regularGram_abs_le μ hQ U H L hU hH w w)
  · rw [hqz]
    exact hqr

end RegularPointCoordinates

end

end OAI
