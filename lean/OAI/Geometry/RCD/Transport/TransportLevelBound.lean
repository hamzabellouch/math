import OAI.Geometry.RCD.Transport.LocalizedPlanEnergy

namespace OAI

/-! # Local level-set bound from the actual RCD transport plan

Transport from a superlevel set to a sublevel set controls the squared
distance to their common level. Only energy in the enlarged ball occurs.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.level_integral_bound
    {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (p : X) {R : ℝ} (hR : 0 < R) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : hausdorff n X A ≠ 0) (hB0 : hausdorff n X B ≠ 0)
    (hsA : A ⊆ closedBall p R) (hsB : B ⊆ closedBall p R)
    {u G : Lp ℝ 2 (hausdorff n X)} (hG : IsRelaxedSlope (hausdorff n X) u G)
    (k : ℝ) (hlevel : ∀ x ∈ A, ∀ y ∈ B, (u x - k) ^ 2 ≤ (u y - u x) ^ 2) :
    (∫ x in A, (u x - k) ^ 2 ∂hausdorff n X) ≤
      (hausdorff n X A).toReal * (2 * R) ^ 2 *
        (compressionBudget K n (2 * R)
          (max (hausdorff n X A)⁻¹ (hausdorff n X B)⁻¹)).toReal *
        (∫ x in ball p (8 * R), (G x) ^ 2 ∂hausdorff n X) := by
  let μ := hausdorff n X
  let C : ℝ≥0∞ := max (μ A)⁻¹ (μ B)⁻¹
  have hAt : μ A ≠ ∞ := (hX.finiteOnBounded A (isBounded_closedBall.subset hsA)).ne
  have hBt : μ B ≠ ∞ := (hX.finiteOnBounded B (isBounded_closedBall.subset hsB)).ne
  have hC : C ≠ ∞ := max_ne_top (ENNReal.inv_ne_top.mpr hA0) (ENNReal.inv_ne_top.mpr hB0)
  let := uniformOn_probability μ A hA0 hAt
  let := uniformOn_probability μ B hB0 hBt
  have hbA : ∀ᵐ x ∂uniformOn μ A, dist x p ≤ R :=
    (uniformOn_ae_mem μ A hA).mono fun x hx => hsA hx
  have hbB : ∀ᵐ x ∂uniformOn μ B, dist x p ≤ R :=
    (uniformOn_ae_mem μ B hB).mono fun x hx => hsB hx
  obtain ⟨π, hπ, hgeo, hopt, hi, hall⟩ := hX.exists_bounded_entropy_plan K n hn
    (uniformOn μ A) (uniformOn μ B) hC (uniformOn_le_scaled μ A (le_max_left _ _))
    (uniformOn_le_scaled μ B (le_max_right _ _)) p hR.le hbA hbB
  let := hπ
  let := hX.separable
  have hend := optimalPlan_endpoints (uniformOn μ A) (uniformOn μ B) π hopt
  have hcap := compressionBudget_ne_top K n (2 * R) hC
  have hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ compressionBudget K n (2 * R) C • μ :=
    fun t => (hall t).1
  have hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π :=
    (memLp_two_iff_integrable_sq (((measurable_path_eval 0).dist
      (measurable_path_eval 1)).aestronglyMeasurable)).mpr hi
  have hDb := optimalPlanDistanceBound_of_bounded
    (uniformOn μ A) (uniformOn μ B) p hbA hbB π hπ hgeo hopt
  have hstay (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x ∈ ball p (8 * R) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_ball).mpr
    filter_upwards [optimal_geodesic_plan_bounded (uniformOn μ A) (uniformOn μ B)
      π hgeo hopt p hR.le hbA hbB] with γ hγ
    have ht := hγ.2 t
    change dist (γ t) p ≤ 3 * R at ht
    change dist (γ t) p < 8 * R
    linarith
  have hsq := hG.testPlan_integrated_square_on μ π hgeo hcap hcomp hD hDb hstay
  have horder : ∀ᵐ γ ∂π, (u (γ 0) - k) ^ 2 ≤ (u (γ 1) - u (γ 0)) ^ 2 := by
    have ha : ∀ᵐ γ ∂π, γ 0 ∈ A := by
      apply ae_of_ae_map (measurable_path_eval 0).aemeasurable
      rw [hend.1]
      exact uniformOn_ae_mem μ A hA
    have hb : ∀ᵐ γ ∂π, γ 1 ∈ B := by
      apply ae_of_ae_map (measurable_path_eval 1).aemeasurable
      rw [hend.2]
      exact uniformOn_ae_mem μ B hB
    filter_upwards [ha, hb] with γ ha hb
    exact hlevel _ ha _ hb
  have hu (t : Time) : MemLp (fun γ : C(Time, X) => u (γ t)) 2 π :=
    compressionPullback_memLp μ π _ (measurable_path_eval t) hcap (hcomp t) u
  have hstart : (∫ γ : C(Time, X), (u (γ 0) - k) ^ 2 ∂π) ≤
      (∫ γ : C(Time, X), (u (γ 1) - u (γ 0)) ^ 2 ∂π) := by
    apply integral_mono_ae ((hu 0).sub (memLp_const k)).integrable_sq
      ((hu 1).sub (hu 0)).integrable_sq
    filter_upwards [horder] with γ hγ
    change (u (γ 0) - k) ^ 2 ≤ (u (γ 1) - u (γ 0)) ^ 2
    exact hγ
  have he : (∫ γ : C(Time, X), (u (γ 0) - k) ^ 2 ∂π) =
      (μ A).toReal⁻¹ * ∫ x in A, (u x - k) ^ 2 ∂μ := by
    calc
      _ = ∫ x, (u x - k) ^ 2 ∂uniformOn μ A := by
        rw [← hend.1]
        exact (integral_map (measurable_path_eval 0).aemeasurable
          (((Lp.stronglyMeasurable u).sub stronglyMeasurable_const).pow 2).aestronglyMeasurable).symm
      _ = _ := by rw [uniformOn, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  have hh := hstart.trans hsq
  rw [he] at hh
  have hpos : 0 < (μ A).toReal := ENNReal.toReal_pos hA0 hAt
  have hmul := mul_le_mul_of_nonneg_left hh hpos.le
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at hmul
  dsimp only [C, μ] at hmul
  simpa only [mul_assoc] using hmul

/-- When the opposite level set has at least as much mass, normalization
of the transport plan cancels exactly from the estimate. -/
theorem NoncollapsedRCD.balanced_level_integral_bound
    {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (p : X) {R : ℝ} (hR : 0 < R) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsA : A ⊆ closedBall p R) (hsB : B ⊆ closedBall p R)
    (hAB : hausdorff n X A ≤ hausdorff n X B)
    {u G : Lp ℝ 2 (hausdorff n X)} (hG : IsRelaxedSlope (hausdorff n X) u G)
    (k : ℝ) (hlevel : ∀ x ∈ A, ∀ y ∈ B, (u x - k) ^ 2 ≤ (u y - u x) ^ 2) :
    (∫ x in A, (u x - k) ^ 2 ∂hausdorff n X) ≤
      (2 * R) ^ 2 * Real.exp ((n : ℝ) * (4 * R) * Real.sqrt (|K| / (n - 1))) *
        (∫ x in ball p (8 * R), (G x) ^ 2 ∂hausdorff n X) := by
  by_cases hA0 : hausdorff n X A = 0
  · rw [Measure.restrict_eq_zero.mpr hA0, integral_zero_measure]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (integral_nonneg fun _ => sq_nonneg _)
  have hB0 : hausdorff n X B ≠ 0 := by
    intro hB0
    rw [hB0] at hAB
    exact hA0 (le_antisymm hAB bot_le)
  have hAt : hausdorff n X A ≠ ∞ :=
    (hX.finiteOnBounded A (isBounded_closedBall.subset hsA)).ne
  have hpos : 0 < ((hausdorff n X) A).toReal := ENNReal.toReal_pos hA0 hAt
  have h := hX.level_integral_bound hn p hR hA hB hA0 hB0 hsA hsB hG k hlevel
  rw [max_eq_left (ENNReal.inv_le_inv.mpr hAB), compressionBudget, compressionStep,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_inv] at h
  convert h using 1
  have hc : (n : ℝ) * (2 * (2 * R)) = (n : ℝ) * (4 * R) := by ring
  rw [hc]
  field_simp


end RegularPointCoordinates

end

end OAI
