import OAI.Geometry.RCD.Metric.LocalBallMeanDerivative

namespace OAI

/-! # Vanishing compression errors retain the sharp mean derivative estimate -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem local_ball_mean_energy_with_factor {n : ℕ} (hn : 0<n)
    {g : Euclidean n → ℝ} {x : Euclidean n} {B : ℝ} (hB : 0<B) {L : ℝ≥0}
    (hg : LipschitzOnWith L g (closedBall x B)) {D : Euclidean n →L[ℝ] ℝ}
    (hd : HasFDerivAt g D x)
    (ν : FiniteMeasure (Euclidean n)) {d θ c V : ℝ}
    (hθ : 0<θ) (hθ1 : θ<1) (hc : 0<c)
    (hν : Tendsto (fun t => (ν : Measure (Euclidean n)).real (closedBall x t)/
      volume.real (closedBall x t)) (𝓝[>] 0) (𝓝 d))
    (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (hlim : Tendsto r atTop (𝓝 0))
    (v : Euclidean n) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 1))
    (hbound : ∀ᶠ k in atTop,
      ((∫ y, g y ∂(euclideanBallDensityLaw (x+r k • v) (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n)))-
       (∫ y, g y ∂(euclideanBallDensityLaw x (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n))))^2≤
        e k*(‖r k • v‖^2*(V/volume.real (ball x (θ*r k)))*
          (ν : Measure (Euclidean n)).real (closedBall x (c*r k)))) :
    (D v)^2≤‖v‖^2*V*((c/θ)^n*d) := by
  have hleft := (local_ball_mean_derivative hB hg hd hθ hθ1 r hr hlim v).pow 2
  have hright' := he.mul ((euclidean_energy_ratio_limit hn ν x hθ hc hν r hr hlim).const_mul (‖v‖^2*V))
  have hright := hright'
  simp only [one_mul] at hright
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hbound] with k hk
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hr k),mul_pow] at hk
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos (hr k))).mpr
  convert hk using 1
  ring


end RegularPointCoordinates

end

end OAI
