import OAI.Geometry.RCD.Metric.LocalDensityOrder
import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # The local pointwise content of the weak Hamilton--Jacobi inequality

A compact radial cutoff and signed-density order retain the original
Sobolev gradient and L2 time derivative on a strict interior ball.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] (μ : Measure X)
  [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem hamilton_jacobi_density_of_tests (z : X) {r : ℝ} (hr : 0 < r)
    (u : SobolevSpace μ Q) (D : Lp ℝ 2 μ)
    (htest : ∀ (φ : X → ℝ) (L : ℝ≥0), LipschitzWith L φ → HasCompactSupport φ →
      tsupport φ ⊆ ball z r → (∀ x, 0 ≤ φ x) →
      weightedGamma μ Q φ u u ≤ 2*(∫ x, φ x*D x ∂μ)) :
    ∀ᵐ x ∂μ.restrict (closedBall z (r/4)),
      (SobolevSpace.minimalSlope μ Q u x)^2 ≤ 2*D x := by
  let f := fun x => 2*D x-localGamma μ Q u u x
  have hfi : IntegrableOn f (ball z r) μ :=
    ((lp_integrableOn_of_finite μ D (ball z r) (measure_ball_lt_top.ne)).const_mul 2).sub
      (localGamma_memL1 μ Q u u).integrableOn
  let χ := BoundedContinuousFunction.ofNormedAddCommGroup (radialCutoff z (r/4))
    (radialCutoff_lipschitz z (by positivity : 0 < r/4)).continuous 1
    (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (radialCutoff_bounds z (r/4) x).1]
                 exact (radialCutoff_bounds z (r/4) x).2)
  have hχs : tsupport χ ⊆ ball z r := by
    apply (show tsupport χ ⊆ closedBall z (2*(r/4)) from ?_).trans
      (closedBall_subset_ball (by linarith))
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    exact hx (radialCutoff_eq_zero z (by positivity : 0 < r/4)
      (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hn)))
  have hpos : ∀ᵐ x ∂μ.restrict (closedBall z (r/4)), 0 ≤ f x := by
    apply local_density_nonneg_of_tests_integrableOn μ isOpen_ball.measurableSet hfi
      isClosed_closedBall.measurableSet (closedBall_subset_ball (by linarith)) χ
      (radialCutoff_lipschitz z (by positivity : 0 < r/4))
      (radialCutoff_hasCompactSupport z (by positivity : 0 < r/4)) hχs
      (fun x => (radialCutoff_bounds z (r/4) x).1)
      (fun x hx => radialCutoff_eq_one z (by positivity : 0 < r/4) (mem_closedBall'.mp hx))
    intro q hq
    obtain ⟨L,hL,hc,hs⟩ := q.property
    have hp : MemLp (q : X → ℝ) 2 μ := q.val.continuous.memLp_of_hasCompactSupport hc
    have hD : Integrable (fun x => (q : X →ᵇ ℝ) x*D x) μ :=
      hp.integrable_mul (Lp.memLp D)
    have hΓ : Integrable (fun x => (q : X →ᵇ ℝ) x*localGamma μ Q u u x) μ :=
      (localGamma_memL1 μ Q u u).bdd_mul q.val.continuous.aestronglyMeasurable
        (Eventually.of_forall q.val.norm_coe_le_norm)
    have he : (∫ x, (q : X →ᵇ ℝ) x*f x ∂μ) =
        2*(∫ x, (q : X →ᵇ ℝ) x*D x ∂μ)-weightedGamma μ Q q u u := by
      change (∫ x, (q : X →ᵇ ℝ) x*(2*D x-localGamma μ Q u u x) ∂μ) = _
      simp_rw [mul_sub,show ∀ x, (q : X →ᵇ ℝ) x*(2*D x)=2*((q : X →ᵇ ℝ) x*D x) from
        fun x => by ring]
      rw [integral_sub (hD.const_mul 2) hΓ,integral_const_mul]
      rfl
    rw [he]
    exact sub_nonneg.mpr (htest q L hL hc hs hq)
  filter_upwards [hpos,ae_restrict_of_ae (localGamma_self μ Q u)] with x hx hΓ
  dsimp only [f] at hx
  rw [hΓ] at hx
  linarith

end RegularPointCoordinates

end

end OAI
