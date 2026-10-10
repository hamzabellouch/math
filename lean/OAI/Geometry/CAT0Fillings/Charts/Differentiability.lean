import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Control

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open MeasureTheory Set

variable {Z X : Type*} [MeasurableSpace Z] [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
lemma signed_chart_control_dominates_on
    (μ : Measure Z) (ν : Measure X) [IsFiniteMeasure ν]
    {φ : Z → X} (hφ : Measurable φ) {s₀ : Set Z}
    (hμ : ∀ᵐ z ∂μ, z ∈ s₀)
    (he : MeasurableEmbedding (fun z : s₀ => φ (z : Z))) {w : Z → ℝ}
    (hw : Integrable w μ)
    (hcontrol : ∀ b : X → ℝ, BoundedLip b →
      |∫ z, w z * b (φ z) ∂μ| ≤ ∫ x, |b x| ∂ν) :
    densityPush μ φ (fun z => |w z|) ≤ ν := by
  let w' := hw.aestronglyMeasurable.mk w
  have heq : w =ᵐ[μ] w' := hw.aestronglyMeasurable.ae_eq_mk
  have hτ : densityPush μ φ (fun z => |w z|) = densityPush μ φ (fun z => |w' z|) := by
    unfold densityPush
    congr 1
    apply withDensity_congr_ae
    exact heq.mono fun z hz => by dsimp only; rw [hz]
  rw [hτ]
  apply signed_chart_control_dominates_on_of_measurable μ ν hφ hμ he
    hw.aestronglyMeasurable.measurable_mk (hw.congr heq)
  intro b hb
  have hi : (∫ z, w' z*b (φ z) ∂μ) = ∫ z, w z*b (φ z) ∂μ :=
    integral_congr_ae (heq.mono fun z hz => by dsimp only; rw [hz])
  rw [hi]
  exact hcontrol b hb
end CAT0Fillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

lemma tangentConeAt_eq_univ_of_density_one (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) : tangentConeAt ℝ s x = univ := by
  apply eq_univ_of_forall
  intro z
  rw [tangentConeAt_eq_biInter_closure]
  simp only [mem_iInter]
  intro U hU
  rw [Metric.mem_closure_iff]
  intro ε hε
  have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z (ε / 2))).Nonempty :=
    Measure.eventually_nonempty_inter_smul_of_density_one μ s x hx _ measurableSet_closedBall
      (measure_closedBall_pos μ z (half_pos hε)).ne'
  have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), r • closedBall z (ε / 2) ⊆ U := by
    apply nhdsWithin_le_nhds
    have h := eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := (0 : E))
      (s := closedBall z (ε / 2)) isBounded_closedBall hU
    filter_upwards [h] with r hr
    simpa using hr
  obtain ⟨r, ⟨y, ys, hy⟩, hrU, hr⟩ :=
    (B₁.and (B₂.and self_mem_nhdsWithin)).exists
  obtain ⟨a, ha, hya⟩ : ∃ a, a ∈ closedBall z (ε / 2) ∧ y = x + r • a := by
    simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
    rcases hy with ⟨a, ha, h⟩
    exact ⟨a, ha, by simp only [h, add_neg_cancel_left]⟩
  refine ⟨a, ?_, ?_⟩
  · have hr0 : r ≠ 0 := ne_of_gt hr
    have hra : r • a ∈ U ∩ (x + ·) ⁻¹' s :=
      ⟨hrU (smul_mem_smul_set ha), by simpa only [mem_preimage, ← hya] using ys⟩
    exact ⟨r⁻¹, mem_univ _, r • a, hra, inv_smul_smul₀ hr0 a⟩
  · exact lt_of_le_of_lt (by simpa [dist_comm] using ha) (half_lt_self hε)

lemma uniqueDiffWithinAt_of_density_one (s : Set E) (x : E)
    (hx : Tendsto (fun r => μ (s ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) : UniqueDiffWithinAt ℝ s x := by
  have ht := tangentConeAt_eq_univ_of_density_one μ s x hx
  rw [uniqueDiffWithinAt_iff, ht]
  exact ⟨by simp, mem_closure_of_nonempty_tangentConeAt (by rw [ht]; exact univ_nonempty)⟩

lemma ae_uniqueDiffWithinAt (s : Set E) :
    ∀ᵐ x ∂μ.restrict s, UniqueDiffWithinAt ℝ s x := by
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div μ s] with x hx
  exact uniqueDiffWithinAt_of_density_one μ s x hx

lemma ae_fderivWithin_eq_fderiv_extension {s : Set E} (hs : MeasurableSet s)
    {f F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (heq : EqOn f F s) :
    ∀ᵐ x ∂μ.restrict s, fderivWithin ℝ f s x = fderiv ℝ F x := by
  filter_upwards [ae_uniqueDiffWithinAt μ s, ae_restrict_mem hs,
    (hF.ae_differentiableAt (μ := μ)).filter_mono (ae_mono Measure.restrict_le_self)]
    with x hx hxs hFx
  rw [fderivWithin_congr' heq hxs, fderivWithin_eq_fderiv hx hFx]

lemma ae_norm_fderivWithin_le {s : Set E} (hs : MeasurableSet s)
    {f : E → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f s) :
    ∀ᵐ x ∂μ.restrict s, ‖fderivWithin ℝ f s x‖ ≤ L := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  filter_upwards [ae_fderivWithin_eq_fderiv_extension μ hs hF heq] with x hx
  rw [hx]
  exact norm_fderiv_le_of_lipschitz ℝ hF

end CAT0Fillings

end

end OAI
