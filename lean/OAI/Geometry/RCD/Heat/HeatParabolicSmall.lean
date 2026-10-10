import OAI.Geometry.RCD.Heat.HeatParabolicDecay

namespace OAI

/-! # Small space-time heat mass gives a local upper bound

Dyadic decay first gives a zero upper-level mass on a fixed later
cylinder. Continuity in time includes its final slice in the estimate.
-/

open Set Filter MeasureTheory Metric
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_small_parabolic_mass_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
    letI : (hausdorff n X).Regular := inferInstance
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : X) (R τ : ℝ), 0 < R → -1 ≤ K*R^2 → 0 < τ →
      ∀ f : Lp ℝ 2 (hausdorff n X),
      (∫ t in τ..(τ+R^2), ∫ y in ball x R, (heatAt (hausdorff n X) hX.quadratic t f y)^2
        ∂hausdorff n X) ≤ δ*(R^2*(hausdorff n X).real (ball x R)) →
      ∀ᵐ y ∂(hausdorff n X).restrict (ball x (R/2)),
        heatAt (hausdorff n X) hX.quadratic (τ+R^2) f y ≤ 1 := by
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let : (hausdorff n X).Regular := inferInstance
  obtain ⟨δ,hδ,hdecay⟩ := hX.heat_parabolic_level_decay hn
  refine ⟨δ,hδ,?_⟩
  intro x R τ hR hcurv hτ f hsmall
  let μ := hausdorff n X
  let A := τ+R^2/4
  let B := τ+R^2
  let H := fun t => ∫ y in ball x (R/2), (max (heatAt μ hX.quadratic t f y-1) 0)^2 ∂μ
  have hAB : A < B := by dsimp only [A,B]; nlinarith [sq_pos_of_pos hR]
  have hHc : Continuous H := continuous_heat_upper_level_mass μ hX.quadratic f zero_le_one measurableSet_ball
  have hHn (t : ℝ) : 0 ≤ H t := integral_nonneg fun y => sq_nonneg _
  have hlim := hdecay x R τ hR hcurv hτ f hsmall
  have hbound (i : ℕ) : (∫ t in A..B, H t) ≤
      ∫ t in (parabolicDyadicTime τ R i)..B, ∫ y in closedBall x (R/2+R/(4*2^i)),
        (max (heatAt μ hX.quadratic t f y-(1-(2^i:ℝ)⁻¹)) 0)^2 ∂μ := by
    have hk := (dyadic_level_gap_bounds hR i).1
    let J := fun t => ∫ y in closedBall x (R/2+R/(4*2^i)),
      (max (heatAt μ hX.quadratic t f y-(1-(2^i:ℝ)⁻¹)) 0)^2 ∂μ
    have hJc : Continuous J := continuous_heat_upper_level_mass μ hX.quadratic f hk measurableSet_closedBall
    have hspace (t : ℝ) : H t ≤ J t := by
      apply heat_upper_level_mass_mono μ hX.quadratic f t hk
        (sub_le_self _ (by positivity))
      exact ball_subset_closedBall.trans
        (closedBall_subset_closedBall (le_add_of_nonneg_right (by positivity)))
    have h1 := intervalIntegral.integral_mono_on hAB.le
      (hHc.intervalIntegrable (μ := volume) A B) (hJc.intervalIntegrable (μ := volume) A B)
      (fun t _ => hspace t)
    have h2 : (∫ t in A..B, J t) ≤ ∫ t in (parabolicDyadicTime τ R i)..B, J t :=
      intervalIntegral.integral_mono_interval (parabolicDyadicTime_bounds (τ := τ) hR i).2.2.2
        hAB.le le_rfl (Eventually.of_forall fun t => integral_nonneg fun y => sq_nonneg _)
        (hJc.intervalIntegrable (μ := volume) _ _)
    exact h1.trans h2
  have hzero : (∫ t in A..B, H t) = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound))
      (intervalIntegral.integral_nonneg_of_forall hAB.le hHn)
  have hHB : H B = 0 := by
    by_contra hz
    have hp : 0 < H B := lt_of_le_of_ne (hHn B) (Ne.symm hz)
    have hh := intervalIntegral.integral_pos hAB hHc.continuousOn
      (fun t _ => hHn t) ⟨B,⟨hAB.le,le_rfl⟩,hp⟩
    rw [hzero] at hh
    exact (lt_irrefl (0:ℝ)) hh
  have hi : Integrable (fun y => (max (heatAt μ hX.quadratic B f y-1) 0)^2) μ :=
    ((upperLevelPart_lipschitz 1).comp_memLp (upperLevelPart_zero zero_le_one)
      (Lp.memLp (heatAt μ hX.quadratic B f))).integrable_sq
  have hz := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hi.integrableOn).mp hHB
  filter_upwards [hz] with y hy
  have hy0 : max (heatAt μ hX.quadratic B f y-1) 0 = 0 := sq_eq_zero_iff.mp hy
  have hh := le_max_left (heatAt μ hX.quadratic B f y-1) 0
  rw [hy0] at hh
  linarith only [hh]

end RegularPointCoordinates

end

end OAI
