import OAI.Geometry.QuadricBundles.RootTrace

namespace OAI

universe u1 u2 u3

noncomputable section

namespace QuadricCounterexample
open Set Metric MeasureTheory Topology Filter
open scoped ENNReal

section BallAverage
variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuous_ball_integral {f : E → F} (hf : Integrable f μ) (r : ℝ) :
    Continuous (fun x ↦ ∫ y in ball x r, f y ∂μ) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x₀
  have hx₀ : ∀ᵐ y ∂μ, y ∉ sphere x₀ r := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using μ.addHaar_sphere x₀ r
  have hbound (x y : E) : ‖(ball x r).indicator f y‖ ≤ ‖f y‖ := by
    by_cases hy : y ∈ ball x r
    · simp only [indicator_of_mem hy]
      exact le_rfl
    · simp only [indicator_of_notMem hy, norm_zero]
      exact norm_nonneg _
  have hcont : ∀ᵐ y ∂μ, ContinuousAt (fun x ↦ (ball x r).indicator f y) x₀ := by
    filter_upwards [hx₀] with y hy
    have hdist : dist y x₀ ≠ r := hy
    rcases lt_or_gt_of_ne hdist with hlt | hgt
    · have hn : ∀ᶠ x in 𝓝 x₀, dist y x < r :=
        (continuous_const.dist continuous_id).continuousAt.eventually_lt_const hlt
      apply (show ContinuousAt (fun _ : E ↦ f y) x₀ from continuousAt_const).congr_of_eventuallyEq
      filter_upwards [hn] with x hx
      simp only [indicator_of_mem (show y ∈ ball x r from hx)]
    · have hn : ∀ᶠ x in 𝓝 x₀, r < dist y x :=
        (continuous_const.dist continuous_id).continuousAt.eventually_const_lt hgt
      apply (show ContinuousAt (fun _ : E ↦ (0 : F)) x₀ from continuousAt_const).congr_of_eventuallyEq
      filter_upwards [hn] with x hx
      simp only [indicator_of_notMem (show y ∉ ball x r from not_lt_of_ge hx.le)]
  have hh : ContinuousAt (fun x ↦ ∫ y, (ball x r).indicator f y ∂μ) x₀ :=
    continuousAt_of_dominated
      (Eventually.of_forall fun x ↦ hf.aestronglyMeasurable.indicator measurableSet_ball)
      (Eventually.of_forall fun x ↦ Eventually.of_forall (hbound x)) hf.norm hcont
  simpa only [integral_indicator measurableSet_ball] using hh

theorem continuous_ball_average {f : E → F} (hf : Integrable f μ) (r : ℝ) :
    Continuous (fun x ↦ ⨍ y in ball x r, f y ∂μ) := by
  simp_rw [setAverage_eq, measureReal_def, μ.addHaar_ball_center]
  exact continuous_const.smul (continuous_ball_integral hf r)

end BallAverage

section Representative
variable {E : Type u3} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [μ.IsAddHaarMeasure] [Nontrivial E] in
lemma ball_average_nonneg {u : E → ℝ} (hu : 0 ≤ᵐ[μ] u) (x : E) (r : ℝ) :
    0 ≤ ⨍ y in ball x r, u y ∂μ := by
  rw [setAverage_eq, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg_of_ae (ae_restrict_of_ae hu))

omit [BorelSpace E] [Nontrivial E] in
lemma ball_average_le_const {u : E → ℝ} {x : E} {r c : ℝ}
    (hr : 0 < r) (hu : IntegrableOn u (ball x r) μ)
    (hle : u ≤ᵐ[μ.restrict (ball x r)] fun _ ↦ c) :
    (⨍ y in ball x r, u y ∂μ) ≤ c := by
  have hfin : μ (ball x r) ≠ ∞ := measure_ne_top_of_subset ball_subset_closedBall
    (isCompact_closedBall x r).measure_ne_top
  have hc : IntegrableOn (fun _ : E ↦ c) (ball x r) μ := integrableOn_const hfin
  calc
    (⨍ y in ball x r, u y ∂μ) ≤ ⨍ _y in ball x r, c ∂μ := by
      simp_rw [setAverage_eq, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (integral_mono_ae hu hc hle)
        (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = c := setAverage_const (ne_of_gt (Metric.measure_ball_pos μ x hr)) hfin c

theorem ball_infimum_representative_limit {u : E → ℝ} (hu : Integrable u μ)
    (hpos : 0 ≤ᵐ[μ] u) {Ω : Set E} (hΩ : IsOpen Ω)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hmean : ∀ n, ∀ᵐ x ∂μ.restrict Ω, u x ≤ ⨍ y in ball x (r n), u y ∂μ) :
    let q := fun x ↦ ⨅ n, ⨍ y in ball x (r n), u y ∂μ
    UpperSemicontinuous q ∧ (∀ x, 0 ≤ q x) ∧
      (∀ᵐ x ∂μ.restrict Ω, u x ≤ q x) ∧
      ∀ x ∈ Ω, Tendsto (fun n ↦ ⨍ y in ball x (r n), u y ∂μ) atTop (𝓝 (q x)) := by
  let A := fun n x ↦ ⨍ y in ball x (r n), u y ∂μ
  have hApos (x : E) (n : ℕ) : 0 ≤ A n x := ball_average_nonneg hpos x (r n)
  have hb (x : E) : BddBelow (range fun n ↦ A n x) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hApos x n⟩
  have hq : UpperSemicontinuous (fun x ↦ ⨅ n, A n x) :=
    upperSemicontinuous_ciInf hb (fun n ↦ (continuous_ball_average hu (r n)).upperSemicontinuous)
  have hle : ∀ᵐ x ∂μ.restrict Ω, u x ≤ ⨅ n, A n x := by
    filter_upwards [ae_all_iff.mpr hmean] with x hx
    exact le_ciInf hx
  refine ⟨hq, fun x ↦ le_ciInf (hApos x), hle, ?_⟩
  intro x hx
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n ↦ ha.trans_le (ciInf_le (hb x) n)
  · intro b hqb
    obtain ⟨c, hqc, hcb⟩ := exists_between hqb
    have hn := inter_mem (hΩ.mem_nhds hx) (hq x c hqc)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
    have hnδ : ∀ᶠ n in atTop, r n < δ := hr0.eventually (gt_mem_nhds hδ)
    filter_upwards [hnδ] with n hn
    have hsub : ball x (r n) ⊆ Ω := fun y hy ↦ (hball (ball_subset_ball hn.le hy)).1
    have huc : u ≤ᵐ[μ.restrict (ball x (r n))] fun _ ↦ c := by
      have hh := ae_mono (Measure.restrict_mono hsub le_rfl) hle
      filter_upwards [hh, ae_restrict_mem measurableSet_ball] with y hy hyb
      exact hy.trans (hball (ball_subset_ball hn.le hyb)).2.le
    exact (ball_average_le_const (hr n) hu.integrableOn huc).trans_lt hcb

lemma ball_average_eq_closedBall_average (u : E → ℝ) (x : E) (r : ℝ) :
    (⨍ y in ball x r, u y ∂μ) = ⨍ y in closedBall x r, u y ∂μ := by
  apply setAverage_congr
  exact ae_eq_of_subset_of_measure_ge ball_subset_closedBall
    (μ.addHaar_closedBall_eq_addHaar_ball x r).le measurableSet_ball.nullMeasurableSet
    (isCompact_closedBall x r).measure_ne_top

theorem ball_infimum_representative_ae {u : E → ℝ} (hu : Integrable u μ)
    (hpos : 0 ≤ᵐ[μ] u) {Ω : Set E} (hΩ : IsOpen Ω)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0))
    (hmean : ∀ n, ∀ᵐ x ∂μ.restrict Ω, u x ≤ ⨍ y in ball x (r n), u y ∂μ) :
    (fun x ↦ ⨅ n, ⨍ y in ball x (r n), u y ∂μ) =ᵐ[μ.restrict Ω] u := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average μ hu.locallyIntegrable 1
  have hlim := (ball_infimum_representative_limit hu hpos hΩ hr hr0 hmean).2.2.2
  have hr' : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr0, Eventually.of_forall hr⟩
  filter_upwards [ae_restrict_of_ae hdiff, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  have hd := hx (fun _ : ℕ ↦ x) r hr' (Eventually.of_forall fun n ↦ by
    simpa only [one_mul] using (mem_closedBall_self (hr n).le))
  simp_rw [← ball_average_eq_closedBall_average] at hd
  exact tendsto_nhds_unique (hlim x hxΩ) hd

end Representative
end QuadricCounterexample

end

end OAI
