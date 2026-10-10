import OAI.Geometry.RCD.Metric.EuclideanBallDensityLaw
import OAI.Geometry.RCD.Sobolev.TranslatedMeanDerivative
import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios

namespace OAI

/-! # Derivatives detected by translated compact ball averages -/

open Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_ball_mean_derivative {n : ℕ} {g : Euclidean n → ℝ}
    (hg : Continuous g) {D : Euclidean n →L[ℝ] ℝ} {x : Euclidean n}
    (hd : HasFDerivAt g D x) {θ : ℝ} (hθ : 0<θ) (hθ1 : θ<1)
    (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (hlim : Tendsto r atTop (𝓝 0))
    (v : Euclidean n) :
    Tendsto (fun k =>
      ((∫ y, g y ∂(euclideanBallDensityLaw (x+r k • v) (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n)))-
       (∫ y, g y ∂(euclideanBallDensityLaw x (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n))))/r k)
      atTop (𝓝 (D v)) := by
  have hh := translated_mean_derivative hg hd zero_le_one r hr hlim
    (fun k => euclideanBallDensityLaw x (b := r k) (mul_pos hθ (hr k)) (by nlinarith [hr k]))
    (fun k => by
      simpa only [one_mul] using (euclideanBallDensityLaw_support x (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]))) v
  simpa only [← euclideanBallDensityLaw_translate] using hh

theorem euclidean_ball_mean_energy_derivative {n : ℕ} (hn : 0<n)
    {g : Euclidean n → ℝ} (hg : Continuous g) {D : Euclidean n →L[ℝ] ℝ}
    {x : Euclidean n} (hd : HasFDerivAt g D x)
    (ν : FiniteMeasure (Euclidean n)) {d θ c V : ℝ}
    (hθ : 0<θ) (hθ1 : θ<1) (hc : 0<c)
    (hν : Tendsto (fun t => (ν : Measure (Euclidean n)).real (closedBall x t)/
      volume.real (closedBall x t)) (𝓝[>] 0) (𝓝 d))
    (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (hlim : Tendsto r atTop (𝓝 0))
    (v : Euclidean n)
    (hbound : ∀ᶠ k in atTop,
      ((∫ y, g y ∂(euclideanBallDensityLaw (x+r k • v) (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n)))-
       (∫ y, g y ∂(euclideanBallDensityLaw x (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n))))^2≤
        ‖r k • v‖^2*(V/volume.real (ball x (θ*r k)))*
          (ν : Measure (Euclidean n)).real (closedBall x (c*r k))) :
    (D v)^2≤‖v‖^2*V*((c/θ)^n*d) := by
  have hleft := (euclidean_ball_mean_derivative hg hd hθ hθ1 r hr hlim v).pow 2
  have hright := (euclidean_energy_ratio_limit hn ν x hθ hc hν r hr hlim).const_mul (‖v‖^2*V)
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
