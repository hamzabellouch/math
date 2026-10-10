import OAI.Probability.SLE.Mass.CanonicalMassContinuity
import OAI.Probability.SLE.Geometry.ConformalRestartTransport

namespace OAI

/-! Bounded compact weights preserve the scalar continuity estimates
used for the canonical disk mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma integral_weight_difference_le
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≤ ν)
    (f : X → ℝ) (hf : Integrable f ν) (M : ℝ)
    (h0 : 0 ≤ᵐ[ν] f) (hM : ∀ᵐ x ∂ν, f x ≤ M) :
    0 ≤ (∫ x, f x ∂ν)-(∫ x, f x ∂μ) ∧
      (∫ x, f x ∂ν)-(∫ x, f x ∂μ) ≤ M*((ν univ).toReal-(μ univ).toReal) := by
  let ξ := ν-μ
  have hξν : ξ ≤ ν := Measure.sub_le
  have hξ : Integrable f ξ := hf.mono_measure hξν
  have hμ : Integrable f μ := hf.mono_measure hμν
  have he : (∫ x, f x ∂ν) = (∫ x, f x ∂ξ)+(∫ x, f x ∂μ) := by
    rw [← sigmaFinite_sub_add_cancel_of_le hμν]
    exact integral_add_measure hξ hμ
  have hn : 0 ≤ ∫ x, f x ∂ξ := integral_nonneg_of_ae (ae_mono hξν h0)
  have hi : (∫ x, f x ∂ξ) ≤ ∫ _ : X, M ∂ξ :=
    integral_mono_ae hξ (integrable_const M) (ae_mono hξν hM)
  have hv : (ξ univ).toReal = (ν univ).toReal-(μ univ).toReal := by
    rw [Measure.sub_apply MeasurableSet.univ hμν,
      ENNReal.toReal_sub_of_le (hμν univ) (measure_ne_top ν univ)]
  simp only [integral_const,smul_eq_mul,measureReal_def,hv] at hi
  constructor
  · linarith
  · rw [mul_comm] at hi
    linarith

namespace Multipoint

lemma compact_weight_bounded (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∃ M : ℝ≥0, ∀ z ∈ K, w z ≤ M := by
  obtain ⟨M,hM⟩ := hK.bddAbove_image w.continuous.continuousOn
  exact ⟨M,fun z hz => hM (mem_image_of_mem _ hz)⟩

lemma compact_weight_integrable (w : C(upperHalfPlane,ℝ≥0))
    (K : Set upperHalfPlane) (hK : IsCompact K)
    (μ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts μ] :
    IntegrableOn (fun z => (w z:ℝ)) K μ :=
  (continuous_subtype_val.comp w.continuous).continuousOn.integrableOn_compact hK

lemma compact_weight_difference_le
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K)
    (M : ℝ≥0) (hM : ∀ z ∈ K, w z ≤ M)
    (μ ν : Measure upperHalfPlane)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (hμν : μ ≤ ν) :
    |(∫ z in K, (w z:ℝ) ∂ν)-(∫ z in K, (w z:ℝ) ∂μ)| ≤
      (M:ℝ)*|(ν K).toReal-(μ K).toReal| := by
  let : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := μ)⟩
  let : IsFiniteMeasure (ν.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := ν)⟩
  have h := integral_weight_difference_le (μ.restrict K) (ν.restrict K)
    (Measure.restrict_mono le_rfl hμν) (fun z => (w z:ℝ))
    (compact_weight_integrable w K hK ν) M
    (ae_of_all _ (fun z => (w z).coe_nonneg))
    ((ae_restrict_mem hK.measurableSet).mono (fun z hz => NNReal.coe_le_coe.mpr (hM z hz)))
  have hv : (μ K).toReal ≤ (ν K).toReal :=
    ENNReal.toReal_mono hK.measure_ne_top (hμν K)
  simpa only [Measure.restrict_apply_univ,abs_of_nonneg h.1,
    abs_of_nonneg (sub_nonneg.mpr hv)] using h.2

theorem ContinuousMassPath.weighted_compact_continuous
    {γ : ℝ≥0 → ℂ} {μ : ℚ → Measure upperHalfPlane} {ν : Measure upperHalfPlane}
    {N : ℝ≥0 → Measure upperHalfPlane} (hp : ContinuousMassPath γ μ ν N)
    (hN : ∀ t, IsFiniteMeasureOnCompacts (N t))
    (w : C(upperHalfPlane,ℝ≥0)) (K : Set upperHalfPlane) (hK : IsCompact K) :
    Continuous (fun t => ∫ z in K, (w z:ℝ) ∂N t) := by
  obtain ⟨M,hM⟩ := compact_weight_bounded w K hK
  apply continuous_iff_continuousAt.mpr
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hpos : 0 < ε/((M:ℝ)+1) := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hvar⟩ := hp.local_variation K hK t₀ _ hpos
  refine ⟨δ,hδ,?_⟩
  intro t ht
  let := hN t
  let := hN t₀
  have ht' : dist (t:ℝ) (t₀:ℝ) < δ := ht
  have hsmall := hvar t t₀ ht' (by simpa using hδ) K hK.measurableSet Subset.rfl
  have hb : |(∫ z in K, (w z:ℝ) ∂N t)-(∫ z in K, (w z:ℝ) ∂N t₀)| ≤
      (M:ℝ)*|((N t) K).toReal-((N t₀) K).toReal| := by
    rcases le_total t t₀ with htt | htt
    · have h := compact_weight_difference_le w K hK M hM (N t) (N t₀) (hp.monotone htt)
      simpa only [abs_sub_comm] using h
    · exact compact_weight_difference_le w K hK M hM (N t₀) (N t) (hp.monotone htt)
  rw [Real.dist_eq]
  have he : ε/((M:ℝ)+1)*((M:ℝ)+1)=ε := div_mul_cancel₀ _ (by positivity)
  nlinarith [abs_nonneg (((N t) K).toReal-((N t₀) K).toReal),M.coe_nonneg]

end Multipoint
end SLEExactGauge

end

end OAI
