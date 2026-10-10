import OAI.Geometry.RCD.Coordinates.FrameEnergyError
import OAI.Geometry.RCD.Coordinates.FrameResidualEnergy

namespace OAI

/-! # Energy bounds for the actual coefficient vector -/

open Set Filter MeasureTheory Finset
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem gradient_frame_coefficients_norm_sq_le {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) {S : Set X}
    (hu : ∀ i, ∀ᵐ x ∂μ.restrict S, localGamma μ hQ (u i) (u i) x≤4) :
    ∀ᵐ x ∂μ.restrict S, ‖gradientFrameCoefficients μ hQ u g x‖^2≤
      4*(n:ℝ)*localGamma μ hQ g g x := by
  have hc (i : Fin n) : ∀ᵐ x ∂μ.restrict S,
      (localGamma μ hQ (u i) g x)^2≤4*localGamma μ hQ g g x := by
    filter_upwards [hu i,ae_restrict_of_ae (localGamma_sq_le μ hQ (u i) g),
      ae_restrict_of_ae (localGamma_self μ hQ g)] with x hx hh he
    exact hh.trans (mul_le_mul_of_nonneg_right hx (by rw [he]; positivity))
  filter_upwards [ae_all_iff.mpr hc] with x hx
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (localGamma μ hQ (u i) g x)^2)≤_
  calc
    _≤∑ _i : Fin n, 4*localGamma μ hQ g g x := sum_le_sum (fun i _ => hx i)
    _=_ := by simp; ring

theorem gradient_frame_coefficients_bounded {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (g : SobolevSpace μ hQ) {S : Set X} {L : ℝ}
    (hu : ∀ i, ∀ᵐ x ∂μ.restrict S, localGamma μ hQ (u i) (u i) x≤4)
    (hg : ∀ᵐ x ∂μ.restrict S, localGamma μ hQ g g x≤L^2) :
    ∀ᵐ x ∂μ.restrict S, ‖gradientFrameCoefficients μ hQ u g x‖^2≤4*(n:ℝ)*L^2 := by
  filter_upwards [gradient_frame_coefficients_norm_sq_le μ hQ u g hu,hg] with x hx hy
  exact hx.trans (mul_le_mul_of_nonneg_left hy (by positivity))

end RegularPointCoordinates

end

end OAI
