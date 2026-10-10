import Mathlib

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma tangentConeAt_pi_eq_univ_of_density_one {ι : Type*} [Fintype ι]
    (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) :
    tangentConeAt ℝ {f : ι → E | ∀ i, f i ∈ s} (fun _ => x) = univ := by
  classical
  apply eq_univ_of_forall
  intro z
  rw [tangentConeAt_eq_biInter_closure]
  simp only [mem_iInter]
  intro U hU
  rw [Metric.mem_closure_iff]
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ i, (s ∩ ({x} + r • closedBall (z i) (ε / 2))).Nonempty := by
    rw [eventually_all]
    intro i
    exact Measure.eventually_nonempty_inter_smul_of_density_one μ s x hx _
      measurableSet_closedBall (measure_closedBall_pos μ (z i) (half_pos hε)).ne'
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r • closedBall z (ε / 2) ⊆ U := by
    apply nhdsWithin_le_nhds
    have h := eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := (0 : ι → E))
      (s := closedBall z (ε / 2)) isBounded_closedBall hU
    filter_upwards [h] with r hr
    simpa using hr
  obtain ⟨r, hr₁, hrU, hr⟩ :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  have H (i : ι) : ∃ a ∈ closedBall (z i) (ε / 2), x + r • a ∈ s := by
    obtain ⟨y, hys, hy⟩ := hr₁ i
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    simpa only [h, add_neg_cancel_left] using hys
  choose a ha has using H
  have haz : a ∈ closedBall z (ε / 2) := by
    rw [mem_closedBall, dist_pi_le_iff (half_pos hε).le]
    exact ha
  refine ⟨a, ?_, ?_⟩
  · have hra : r • a ∈ U ∩ ((fun _ : ι => x) + ·) ⁻¹' {f | ∀ i, f i ∈ s} := by
      exact ⟨hrU (smul_mem_smul_set haz), has⟩
    exact ⟨r⁻¹, mem_univ _, r • a, hra, inv_smul_smul₀ (ne_of_gt hr) a⟩
  · exact lt_of_le_of_lt (by simpa [dist_comm] using haz) (half_lt_self hε)

omit [MeasurableSpace E] [BorelSpace E] in

lemma seminorm_continuous_finiteDimensional (p : Seminorm ℝ E) : Continuous p := by
  classical
  let b := Module.finBasis ℝ E
  have hsum (I : Finset (Fin (Module.finrank ℝ E)))
      (q : Fin (Module.finrank ℝ E) → E) :
      p (∑ i ∈ I, q i) ≤ ∑ i ∈ I, p (q i) := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
  have hb (v : E) : p v ≤ ∑ i, ‖b.repr v i‖ * p (b i) := by
    convert hsum Finset.univ (fun i => b.repr v i • b i) using 1
    · rw [b.sum_repr]
    · simp only [map_smul_eq_mul]
  have hcont : Continuous (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp b.continuous_coe_repr).norm.mul_const _
  apply Seminorm.continuous_of_continuousAt_zero
  have hc : Tendsto (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto 0
  simpa [ContinuousAt] using tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hc (fun v => apply_nonneg p v) hb

end CAT0Fillings
end

end OAI
