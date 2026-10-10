import OAI.Geometry.RCD.Coordinates.HarmonicFrameApproximation
import OAI.Geometry.RCD.Coordinates.CenteredFrameGramBound
import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Convergence of the prescribed centered first-order splitting maps -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_frame_convergence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1 ≤ K*(80*r k)^2)
    (hε : ∀ k, 0 ≤ ε k) (hε1 : ∀ k, ε k ≤ 1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 5 (ε k) (V k))
    (u : ℕ → Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : ℕ → X → Euclidean n)
    (hsplit : ∀ k, FirstOrderSplittingOn (hausdorff n X) hX.quadratic
      (p k) (80*r k) (ε k) (u k) (v k)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop,
      IsPointedApproximation (p k) 0 (r k) (5/2) τ
        (fun x => (r k)⁻¹ • (v k x-v k (p k))) := by
  let μ := hausdorff n X
  obtain ⟨D,hD,hvol⟩ := hX.rescaled_ball_volume_factor hn (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<1/16) (by norm_num : (1/16:ℝ)≤1)
  have hvol' (k : ℕ) : μ.real (ball (p k) (80*r k)) ≤ D*μ.real (ball (p k) (5*r k)) := by
    have hh := hvol (p k) (80*r k) (mul_pos (by norm_num) (hr k)) (hcurv k) (p k)
      (by simpa only [dist_self] using (mul_nonneg (by norm_num : (0:ℝ)≤80) (hr k).le))
    simpa only [show (1/16:ℝ)*(80*r k)=5*r k by ring] using hh
  have hex (k : ℕ) := hX.centered_first_order_frame hn (hr k) (hε k) (hε1 k)
    (u k) (v k) (hsplit k)
  choose w hw hrep hnorm he using hex
  have hcurv' (k : ℕ) : -1 ≤ K*(r k)^2 := by
    by_cases hK : 0≤K
    · exact (by norm_num : (-1:ℝ)≤0).trans (mul_nonneg hK (sq_nonneg _))
    · have hh := hcurv k
      nlinarith
  have hv (k : ℕ) : ContinuousOn (fun x => (r k)⁻¹ • (v k x-v k (p k)))
      (ball (p k) (5*r k)) := by
    have hs : ball (p k) (5*r k) ⊆ ball (p k) (80*r k) :=
      ball_subset_ball (by linarith [hr k])
    exact (((hsplit k).continuous.mono hs).sub
      (show ContinuousOn (fun _ : X => v k (p k)) (ball (p k) (5*r k)) from
        continuousOn_const)).const_smul (r k)⁻¹
  have hgram (i j : Fin n) : Tendsto (fun k => (μ.real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (4*r k),
        |r k^2*localGamma μ hX.quadratic (w k i) (w k j) x-(if i=j then 1 else 0)| ∂μ)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro k
      exact mul_nonneg (inv_nonneg.mpr measureReal_nonneg) (integral_nonneg (fun x => abs_nonneg _))
    · intro k
      exact centered_frame_gram_bound hX (hr k) (hε k) (u k) (w k) (v k)
        (hsplit k) (hvol' k) (he k) i j
    · simpa only [mul_zero] using hεlim.const_mul D
  exact hX.harmonic_frame_approximation hn p r ε V
    (fun k x => (r k)⁻¹ • (v k x-v k (p k))) hr hcurv' hε hε1 hεlim hV
    (fun i k => w k i) (fun i k => hw k i) (by norm_num : (0:ℝ)<10)
    (fun i k => hnorm k i) hv (fun k => by simp) (fun i k => hrep k i) hgram

end RegularPointCoordinates

end

end OAI
