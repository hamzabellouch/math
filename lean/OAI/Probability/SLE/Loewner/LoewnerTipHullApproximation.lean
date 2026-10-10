import OAI.Probability.SLE.Geometry.HalfPlaneBoundaryDerivative
import OAI.Probability.SLE.Loewner.LoewnerHeightClearance
import OAI.Probability.SLE.Loewner.LoewnerInverseDriverContinuity

namespace OAI

/-! Kernel convergence cannot leave a fixed surviving ball around the
limiting tip. The boundary derivative estimate gives a quantitative
contradiction to such a ball. -/
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem inverse_convergence_excludes_common_tip_ball
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (h : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n))
    {V : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0)
    (hl : TendstoLocallyUniformlyOn (fun n => F n T) (J T) atTop upperHalfPlane)
    {r : ℝ} (hr : 0 < r) :
    ¬ ∀ n, ball (β T) r ⊆ survivingDomain (γ n) T := by
  intro hballs
  have hnear : ∀ᶠ y : ℝ in 𝓝[>] 0,
      dist (J T ((V T : ℂ)+(y : ℂ)*Complex.I)) (β T) < r/4 :=
    (hv.2.2.2.2.2.2.2.2.2.2.2.2 T).eventually (ball_mem_nhds _ (by positivity))
  have hbound : ∀ᶠ y : ℝ in 𝓝[>] 0,
      r/2 ≤ (128*Real.pi)*(y*‖deriv (J T) ((V T : ℂ)+(y : ℂ)*Complex.I)‖) := by
    filter_upwards [hnear,self_mem_nhdsWithin] with y hy hy0
    let w : ℂ := (V T : ℂ)+(y : ℂ)*Complex.I
    have hw : w ∈ upperHalfPlane := by simpa [w,upperHalfPlane] using hy0
    have hvalue := hl.tendsto_at hw
    have hd := ((hl.deriv (Eventually.of_forall fun n => (h n).2.2.2.2.1 T)
      isOpen_upperHalfPlane).tendsto_at hw).norm
    have hb : ∀ᶠ n in atTop, r/2 ≤ (128*Real.pi)*y*‖deriv (F n T) w‖ := by
      filter_upwards [hvalue.eventually (ball_mem_nhds _ (by positivity : 0 < r/4))]
        with n hn
      have hball : ball (F n T w) (r/2) ⊆ survivingDomain (γ n) T := by
        intro z hz
        apply hballs n
        rw [mem_ball] at hz ⊢
        have ht := dist_triangle z (F n T w) (β T)
        have ht' := dist_triangle (F n T w) (J T w) (β T)
        change dist (F n T w) (J T w) < r/4 at hn
        change dist (J T w) (β T) < r/4 at hy
        linarith
      simpa only [w,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_re,Complex.I_im,mul_one,mul_zero,
        zero_add,add_zero] using (h n).inverse_clearance_bound T hw
          (by positivity : 0 < r/2) hball
    have hh := ge_of_tendsto (hd.const_mul ((128*Real.pi)*y)) hb
    simpa only [mul_assoc] using hh
  have hzero : r/2 ≤ 0 := by
    have hh := ge_of_tendsto ((hv.inverse_tip_derivative_vanishes T).const_mul
      (128*Real.pi)) hbound
    simpa only [mul_zero] using hh
  linarith

theorem driver_neighborhood_hits_tip_hull
    {V : ℝ≥0 → ℝ} {β : ℝ≥0 → ℂ} {H J : ℝ≥0 → ℂ → ℂ}
    (hv : IsCapacityTwoWitness V β H J) (T : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
      (G F : ℝ≥0 → ℂ → ℂ), IsCapacityTwoWitness U γ G F →
      (∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) →
      ¬ ball (β T) r ⊆ survivingDomain γ T := by
  classical
  by_contra hn
  push Not at hn
  have hc (n : ℕ) := hn ((n+1:ℝ)⁻¹) (by positivity)
  choose U γ G F hw hclose hball using hc
  have hδ : Tendsto (fun n : ℕ => (n+1:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hl := inverse_maps_locally_uniform_of_drivers U γ G F hw hv T
    (fun n : ℕ => (n+1:ℝ)⁻¹) hδ hclose
  exact inverse_convergence_excludes_common_tip_ball U γ G F hw hv T hl hr hball

end SLEExactGauge

end

end OAI
