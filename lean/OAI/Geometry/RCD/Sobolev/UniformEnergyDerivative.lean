import OAI.Geometry.RCD.Sobolev.UniformBallEnergyTest
import OAI.Geometry.RCD.Sobolev.SharpLinearEnergyBound
import OAI.Geometry.RCD.Sobolev.LocalMeanEnergyFactor

namespace OAI

/-! # Pointwise lower energy bound for the actual RCD value limit -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.uniform_energy_density_dominates_derivative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hτR : τ<R) (hRS : R<S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    (ν : FiniteMeasure (Euclidean n))
    (henergy : Tendsto (fun k => (localEnergyMeasure (hausdorff n X) hX.quadratic (w k)
      (closedBall (p k) (R*r k))
      (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))).map (v k)) atTop (𝓝 ν))
    (z : Euclidean n) (hz : ‖z‖<ρ)
    (D : Euclidean n →L[ℝ] ℝ) (hD : HasFDerivAt g D z) {d : ℝ}
    (hν : Tendsto (fun t => (ν : Measure (Euclidean n)).real (closedBall z t)/
      volume.real (closedBall z t)) (𝓝[>] 0) (𝓝 d)) :
    ‖D‖^2≤volume.real (ball (0:Euclidean n) S)*d := by
  have hd : 0≤d := ge_of_tendsto hν (Eventually.of_forall fun t =>
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hV : 0≤volume.real (ball (0:Euclidean n) S) := ENNReal.toReal_nonneg
  apply sharp_linear_energy_bound D (mul_nonneg hV hd)
  intro ξ θ hθ hθ1 c hc
  have hc0 : 0<c := lt_trans (by positivity : (0:ℝ)<1+‖ξ‖) hc
  let q : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hq : ∀ k, 0<q k := fun k => by dsimp only [q]; positivity
  have hqlim : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let W := (ρ+S)/2
  let B := (W-‖z‖)/2
  have hρS : ρ<S := hρτ.trans (hτR.trans hRS)
  have hWS : W<S := by dsimp only [W]; linarith
  have hρW : ρ<W := by dsimp only [W]; linarith
  have hB : 0<B := by dsimp only [B]; linarith
  obtain ⟨L,hL⟩ := hg W hWS
  have hsub : closedBall z B⊆closedBall (0:Euclidean n) W := by
    intro y hy
    have ht := dist_triangle y z 0
    simp only [dist_zero_right] at ht
    have hd : dist y z≤B := hy
    simp only [mem_closedBall,dist_zero_right]
    dsimp only [B] at hd
    linarith
  have hlocal := hL.mono hsub
  let e : ℕ → ℝ := fun k => Real.exp ((n:ℝ)*4*(q k+‖q k • ξ‖))
  have helm : Tendsto e atTop (𝓝 1) := by
    have ht : Tendsto (fun k => (n:ℝ)*4*(q k+‖q k • ξ‖)) atTop (𝓝 0) := by
      simp_rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hq _)]
      simpa only [zero_mul,add_zero,mul_zero] using
        (hqlim.add (hqlim.mul_const ‖ξ‖)).const_mul ((n:ℝ)*4)
    simpa only [Function.comp_def,Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp ht
  have hmean := local_ball_mean_energy_with_factor (V := volume.real (ball (0:Euclidean n) S))
    (by omega : 0<n) hB hlocal hD ν
    hθ hθ1 hc0 hν q hq hqlim ξ e helm
  have he : ∀ᶠ k in atTop, ‖z‖+q k*(1+‖ξ‖)<ρ := by
    have ht : Tendsto (fun k => ‖z‖+q k*(1+‖ξ‖)) atTop (𝓝 ‖z‖) := by
      simpa only [zero_mul,add_zero] using (hqlim.mul_const (1+‖ξ‖)).const_add ‖z‖
    exact ht.eventually (Iio_mem_nhds hz)
  have heroom : ∀ᶠ k in atTop, τ+2*(q k*(1+‖ξ‖))<S := by
    have ht : Tendsto (fun k => τ+2*(q k*(1+‖ξ‖))) atTop (𝓝 τ) := by
      simpa only [zero_mul,mul_zero,add_zero] using
        ((hqlim.mul_const (1+‖ξ‖)).const_mul 2).const_add τ
    exact ht.eventually (Iio_mem_nhds (hτR.trans hRS))
  have hb : ∀ᶠ k in atTop,
      ((∫ y, g y ∂(euclideanBallDensityLaw (z+q k • ξ) (b := q k)
        (mul_pos hθ (hq k)) (by nlinarith [hq k]) : Measure (Euclidean n)))-
       (∫ y, g y ∂(euclideanBallDensityLaw z (b := q k)
        (mul_pos hθ (hq k)) (by nlinarith [hq k]) : Measure (Euclidean n))))^2≤
        e k*(‖q k • ξ‖^2*(volume.real (ball (0:Euclidean n) S)/volume.real (ball z (θ*q k)))*
          (ν : Measure (Euclidean n)).real (closedBall z (c*q k))) := by
    filter_upwards [he,heroom] with k hk hkroom
    apply hX.uniform_ball_energy_test hn hS hτ hρτ hτR hRS
      p r ε v hr hcurv hε hε1 hεlim hv w g hg hconv ν henergy z (q k • ξ)
      (mul_pos hθ (hq k)) (by nlinarith [hq k])
    · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hq k)]
      nlinarith only [hk]
    · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hq k)]
      nlinarith only [mul_pos (sub_pos.mpr hc) (hq k)]
    · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hq k)]
      nlinarith only [hkroom]
    · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hq k)]
      nlinarith only [hk,hρτ,hτR]
  have hh := hmean hb
  nlinarith only [hh]

end RegularPointCoordinates

end

end OAI
