import OAI.Geometry.RCD.Metric.EuclideanBallMeanDerivative

namespace OAI

/-! # Shrinking mean derivatives require only local Lipschitz regularity -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem local_ball_mean_derivative {n : ℕ} {g : Euclidean n → ℝ}
    {x : Euclidean n} {B : ℝ} (hB : 0<B) {L : ℝ≥0}
    (hg : LipschitzOnWith L g (closedBall x B))
    {D : Euclidean n →L[ℝ] ℝ} (hd : HasFDerivAt g D x)
    {θ : ℝ} (hθ : 0<θ) (hθ1 : θ<1)
    (r : ℕ → ℝ) (hr : ∀ k, 0<r k) (hlim : Tendsto r atTop (𝓝 0))
    (v : Euclidean n) :
    Tendsto (fun k =>
      ((∫ y, g y ∂(euclideanBallDensityLaw (x+r k • v) (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n)))-
       (∫ y, g y ∂(euclideanBallDensityLaw x (b := r k)
        (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n))))/r k)
      atTop (𝓝 (D v)) := by
  obtain ⟨G,hG,he⟩ := hg.extend_real
  have heq : G=ᶠ[𝓝 x] g := by
    filter_upwards [closedBall_mem_nhds x hB] with y hy
    exact (he hy).symm
  have hDG := hd.congr_of_eventuallyEq heq
  have hm := euclidean_ball_mean_derivative hG.continuous hDG hθ hθ1 r hr hlim v
  apply hm.congr'
  have ht : Tendsto (fun k => r k*(1+‖v‖)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hlim.mul_const (1+‖v‖)
  filter_upwards [ht.eventually (Iio_mem_nhds hB)] with k hk
  have hsmall : r k<B := lt_of_le_of_lt (by nlinarith [mul_nonneg (hr k).le (norm_nonneg v)]) hk
  have hP := euclideanBallDensityLaw_support x (b := r k)
    (mul_pos hθ (hr k)) (show θ*r k<r k by nlinarith [hr k])
  have hQ := euclideanBallDensityLaw_support (x+r k • v) (b := r k)
    (mul_pos hθ (hr k)) (show θ*r k<r k by nlinarith [hr k])
  have hPe : (∫ y, G y ∂(euclideanBallDensityLaw x (b := r k)
      (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n)))=
      ∫ y, g y ∂(euclideanBallDensityLaw x (b := r k)
      (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n)) := by
    apply integral_congr_ae
    exact hP.mono fun y hy => (he (hy.trans hsmall.le)).symm
  have hQe : (∫ y, G y ∂(euclideanBallDensityLaw (x+r k • v) (b := r k)
      (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n)))=
      ∫ y, g y ∂(euclideanBallDensityLaw (x+r k • v) (b := r k)
      (mul_pos hθ (hr k)) (by nlinarith [hr k]) : Measure (Euclidean n)) := by
    apply integral_congr_ae
    apply hQ.mono
    intro y hy
    apply (he ?_).symm
    have ht' := dist_triangle y (x+r k • v) x
    have hs : dist (x+r k • v) x=r k*‖v‖ := by
      simp [dist_eq_norm,norm_smul,abs_of_pos (hr k)]
    change dist y x≤B
    rw [hs] at ht'
    nlinarith
  rw [hPe,hQe]

theorem local_ball_mean_energy_derivative {n : ℕ} (hn : 0<n)
    {g : Euclidean n → ℝ} {x : Euclidean n} {B : ℝ} (hB : 0<B) {L : ℝ≥0}
    (hg : LipschitzOnWith L g (closedBall x B)) {D : Euclidean n →L[ℝ] ℝ}
    (hd : HasFDerivAt g D x)
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
  have hleft := (local_ball_mean_derivative hB hg hd hθ hθ1 r hr hlim v).pow 2
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
