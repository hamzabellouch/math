import OAI.Geometry.RCD.Transport.PlanGradientMean

namespace OAI

/-! # Bounded relaxed gradients give Lipschitz representatives on RCD spaces -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

/-- Transport between small balls controls their averages by the weak
upper gradient, with no volume-comparison factor. -/
theorem NoncollapsedRCD.average_bound_of_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {u G : Lp ℝ 2 (hausdorff n X)} (hG : IsRelaxedSlope (hausdorff n X) u G)
    (L : ℝ≥0) (hGb : ∀ᵐ x ∂hausdorff n X, G x ≤ L) (x y : X) (r : ℝ) (hr : 0 < r) :
    |(⨍ z in closedBall x r, u z ∂hausdorff n X)-
      (⨍ z in closedBall y r, u z ∂hausdorff n X)| ≤ L*(dist x y+2*r) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.Regular := inferInstance
  let A := closedBall x r
  let B := closedBall y r
  have hA0 : μ A ≠ 0 := ((hX.fullSupport x r hr).trans_le (measure_mono ball_subset_closedBall)).ne'
  have hB0 : μ B ≠ 0 := ((hX.fullSupport y r hr).trans_le (measure_mono ball_subset_closedBall)).ne'
  have hAt : μ A ≠ ∞ := (hX.finiteOnBounded A isBounded_closedBall).ne
  have hBt : μ B ≠ ∞ := (hX.finiteOnBounded B isBounded_closedBall).ne
  let := uniformOn_probability μ A hA0 hAt
  let := uniformOn_probability μ B hB0 hBt
  let C : ℝ≥0∞ := max (μ A)⁻¹ (μ B)⁻¹
  have hC : C ≠ ∞ := max_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr hB0)
  have ha : ∀ᵐ z ∂uniformOn μ A, dist z x ≤ dist x y+r := by
    filter_upwards [uniformOn_ae_mem μ A measurableSet_closedBall] with z hz
    exact hz.trans (le_add_of_nonneg_left dist_nonneg)
  have hb : ∀ᵐ z ∂uniformOn μ B, dist z x ≤ dist x y+r := by
    filter_upwards [uniformOn_ae_mem μ B measurableSet_closedBall] with z hz
    have hzy : dist z y ≤ r := hz
    calc
      dist z x ≤ dist z y+dist y x := dist_triangle _ _ _
      _ ≤ r+dist y x := by linarith
      _ = dist x y+r := by rw [dist_comm y x,add_comm]
  obtain ⟨π,hπ,hgeo,hopt,hi,hall⟩ := hX.exists_bounded_entropy_plan K n hn
    (uniformOn μ A) (uniformOn μ B) hC (uniformOn_le_scaled μ A (le_max_left _ _))
    (uniformOn_le_scaled μ B (le_max_right _ _)) x (by positivity) ha hb
  let := hπ
  have hend := optimalPlan_endpoints (uniformOn μ A) (uniformOn μ B) π hopt
  let C' := compressionBudget K n (2*(dist x y+r)) C
  have hC' : C' ≠ ∞ := compressionBudget_ne_top K n (2*(dist x y+r)) hC
  have hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C' • μ := fun t => (hall t).1
  have hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π :=
    (memLp_two_iff_integrable_sq (((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable)).mpr hi
  have hDb : ∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ dist x y+2*r := by
    have ha' : ∀ᵐ γ ∂π, γ 0 ∈ A := by
      apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
      rw [hend.1]
      exact uniformOn_ae_mem μ A measurableSet_closedBall
    have hb' : ∀ᵐ γ ∂π, γ 1 ∈ B := by
      apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
      rw [hend.2]
      exact uniformOn_ae_mem μ B measurableSet_closedBall
    filter_upwards [ha',hb'] with γ ha hb
    have h0 : dist (γ 0) x ≤ r := ha
    have h1 : dist (γ 1) y ≤ r := hb
    have ht := dist_triangle4 (γ 0) x y (γ 1)
    rw [dist_comm y (γ 1)] at ht
    linarith
  have hm := hG.testPlan_mean_increment_le μ π hgeo hC' hcomp hD L.coe_nonneg hDb hGb
  have hu (t : Time) : Integrable (fun γ : C(Time,X) => u (γ t)) π :=
    (compressionPullback_memLp μ π _ (measurable_path_eval t) hC' (hcomp t) u).integrable (by norm_num)
  have hmean : |(∫ γ : C(Time,X), u (γ 1) ∂π)-(∫ γ : C(Time,X), u (γ 0) ∂π)| ≤
      (dist x y+2*r)*L := by
    rw [← integral_sub (hu 1) (hu 0)]
    exact (abs_integral_le_integral_abs).trans hm
  have he (t : Time) (D : Set X) (ht : π.map (fun γ => γ t) = uniformOn μ D) :
      (∫ γ : C(Time,X), u (γ t) ∂π) = ⨍ z in D, u z ∂μ := by
    rw [← integral_map (measurable_path_eval t).aemeasurable (Lp.stronglyMeasurable u).aestronglyMeasurable,ht]
    rw [average_eq',Measure.restrict_apply_univ]
    rfl
  rw [he 0 A hend.1,he 1 B hend.2,abs_sub_comm] at hmean
  simpa only [mul_comm] using hmean

/-- The RCD Sobolev-to-Lipschitz implication needed for the heat kernel. -/
theorem NoncollapsedRCD.lipschitz_of_bounded_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {u G : Lp ℝ 2 (hausdorff n X)} (hG : IsRelaxedSlope (hausdorff n X) u G)
    (L : ℝ≥0) (hGb : ∀ᵐ x ∂hausdorff n X, G x ≤ L) :
    ∃ v : X → ℝ, LipschitzWith L v ∧ u =ᵐ[hausdorff n X] v := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  exact exists_lipschitz_of_average_bound u ((Lp.memLp u).locallyIntegrable (by norm_num)) L
    (hX.average_bound_of_gradient K n hn hG L hGb)

end RegularPointCoordinates

end

end OAI
