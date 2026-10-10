import OAI.Geometry.RCD.Transport.LocalPlanGradientMean

namespace OAI

/-! # Local bounded gradients and Lipschitz representatives -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

/-- Transport between small balls controls their averages by the weak
upper gradient, with no volume-comparison factor. -/
theorem NoncollapsedRCD.local_average_bound_of_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {u G : Lp ℝ 2 (hausdorff n X)} (hG : IsRelaxedSlope (hausdorff n X) u G)
    (L : ℝ≥0) {p : X} {R : ℝ} (hR : 0 < R)
    (hGb : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * R)), G x ≤ L)
    (x y : X) (hx : x ∈ closedBall p R) (hy : y ∈ closedBall p R)
    (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
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
  have ha : ∀ᵐ z ∂uniformOn μ A, dist z p ≤ 2 * R := by
    filter_upwards [uniformOn_ae_mem μ A measurableSet_closedBall] with z hz
    have hzx : dist z x ≤ r := hz
    have hxp : dist x p ≤ R := hx
    linarith [dist_triangle z x p]
  have hb : ∀ᵐ z ∂uniformOn μ B, dist z p ≤ 2 * R := by
    filter_upwards [uniformOn_ae_mem μ B measurableSet_closedBall] with z hz
    have hzy : dist z y ≤ r := hz
    have hyp : dist y p ≤ R := hy
    linarith [dist_triangle z y p]
  obtain ⟨π,hπ,hgeo,hopt,hi,hall⟩ := hX.exists_bounded_entropy_plan K n hn
    (uniformOn μ A) (uniformOn μ B) hC (uniformOn_le_scaled μ A (le_max_left _ _))
    (uniformOn_le_scaled μ B (le_max_right _ _)) p (by positivity) ha hb
  let := hπ
  have hend := optimalPlan_endpoints (uniformOn μ A) (uniformOn μ B) π hopt
  let C' := compressionBudget K n (2*(2*R)) C
  have hC' : C' ≠ ∞ := compressionBudget_ne_top K n (2*(2*R)) hC
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
  have hstay (t : Time) : ∀ᵐ z ∂π.map (fun γ => γ t), z ∈ ball p (8 * R) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_ball).mpr
    filter_upwards [optimal_geodesic_plan_bounded (uniformOn μ A) (uniformOn μ B)
      π hgeo hopt p (by positivity) ha hb] with γ hγ
    have ht : dist (γ t) p ≤ 3 * (2 * R) := hγ.2 t
    change dist (γ t) p < 8 * R
    linarith
  have hm := hG.testPlan_mean_increment_on μ π hgeo hC' hcomp hD L.coe_nonneg hDb hstay hGb
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


/-- Differentiation of local ball averages gives a sharp Lipschitz
representative on the inner ball. No amplitude bound is needed. -/
theorem NoncollapsedRCD.local_lipschitz_representative
    {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    {u G : Lp ℝ 2 (hausdorff n X)} (hG : IsRelaxedSlope (hausdorff n X) u G)
    (L : ℝ≥0) {p : X} {R : ℝ} (hR : 0 < R)
    (hGb : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8 * R)), G x ≤ L) :
    ∃ v : X → ℝ, LipschitzWith L v ∧
      u =ᵐ[(hausdorff n X).restrict (closedBall p R)] v := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  let S := {x : X | Tendsto (fun r : ℝ => ⨍z in closedBall x r, u z ∂μ)
    (𝓝[>] 0) (𝓝 (u x))}
  have hS : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ
      ((Lp.memLp u).locallyIntegrable (by norm_num)) (1 : ℝ)] with x hx
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall, dist_self, one_mul]
      exact hr.le)
  have hl : LipschitzOnWith L u (S ∩ closedBall p R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hc : Tendsto (fun r : ℝ => L * (dist x y + 2 * r)) (𝓝[>] 0)
        (𝓝 (L * dist x y)) := by
      have hh : Continuous (fun r : ℝ => (L : ℝ) * (dist x y + 2 * r)) := by fun_prop
      simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < R :=
      (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
    have hb : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        |(⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, u z ∂μ)| ≤
          L * (dist x y + 2 * r) := by
      filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
      exact hX.local_average_bound_of_gradient K n hn hG L hR hGb x y hx.2 hy.2 r hr hrR.le
    simpa only [Real.dist_eq] using
      le_of_tendsto_of_tendsto ((hx.1.sub hy.1).abs) hc hb
  obtain ⟨v, hv, he⟩ := hl.extend_real
  refine ⟨v, hv, ?_⟩
  filter_upwards [ae_restrict_of_ae hS, ae_restrict_mem measurableSet_closedBall] with x hx hxR
  exact he ⟨hx, hxR⟩

end RegularPointCoordinates

end

end OAI
