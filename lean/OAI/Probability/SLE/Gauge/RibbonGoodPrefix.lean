import OAI.Probability.SLE.Gauge.ActualRibbonHistory

namespace OAI

/-! Narrow actual prefixes are measurable in the possibly infinite front
past. They are exactly the physical information used to reconstruct the
history at the next integer front. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates FirstFrontPassage FrontSuccessMeasurability

local instance goodPrefixPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance goodPrefixPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def ribbonCore (P : ℂ → ℂ) (ε : ℝ) : Set ℂ :=
  P '' {z ∈ closedRibbon | |z.im| ≤ ε}

lemma ribbonCore_isClosed (P : ℂ → ℂ)
    (he : Topology.IsClosedEmbedding (fun z : closedRibbon => P z)) (ε : ℝ) :
    IsClosed (ribbonCore P ε) := by
  have hs : IsClosed {z : closedRibbon | |(z : ℂ).im| ≤ ε} :=
    isClosed_le (Complex.continuous_im.comp continuous_subtype_val).abs continuous_const
  have hh := he.isClosedMap _ hs
  have hset : (fun z : closedRibbon => P z) '' {z : closedRibbon | |(z : ℂ).im| ≤ ε} =
      ribbonCore P ε := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z, ⟨z.2, hz⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hi⟩, rfl⟩
      exact ⟨⟨z, hz⟩, hi, rfl⟩
  exact hset ▸ hh

def GoodRibbonPrefix {Ω : Type*} (γ : Ω → ℝ≥0 → ℂ)
    (τ : Ω → WithTop ℝ≥0) (P : ℂ → ℂ) (ε : ℝ) : Set Ω :=
  {ω | τ ω ≠ ⊤ ∧ MapsTo (γ ω) (Icc 0 ((τ ω).untopD 0)) (ribbonCore P ε) ∧
    γ ω ((τ ω).untopD 0) ∈ ribbonCore P (ε / 4)}

lemma stoppedAtPath_eval_time (f : C(ℝ≥0, ℂ)) (τ : WithTop ℝ≥0) :
    stoppedAtPath f τ (τ.untopD 0) = f (τ.untopD 0) := by
  cases τ with
  | top => simp only [stoppedAtPath, ite_true]
  | coe t => simp only [stoppedAtPath, WithTop.coe_ne_top, ite_false, WithTop.untopD_coe,
      clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk, min_self, zero_le,
      max_eq_right]

lemma stoppedAtPath_range_iff (f : C(ℝ≥0, ℂ)) (t : ℝ≥0) (K : Set ℂ) :
    MapsTo (stoppedAtPath f (t : WithTop ℝ≥0)) univ K ↔ MapsTo f (Icc 0 t) K := by
  simp only [stoppedAtPath, WithTop.coe_ne_top, ite_false, WithTop.untopD_coe]
  constructor
  · intro h u hu
    have hh := h (mem_univ u)
    simpa only [clampedPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      min_eq_left hu.2, max_eq_right hu.1] using hh
  · intro h u _
    exact h ⟨le_max_left _ _, max_le bot_le (min_le_right _ _)⟩

lemma measurableSet_path_range_closed
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (K : Set ℂ) (hK : IsClosed K) :
    MeasurableSet {ω | MapsTo (f ω) univ K} := by
  have hclosed : IsClosed {p : C(ℝ≥0, ℂ) | MapsTo p univ K} := by
    have he : {p : C(ℝ≥0, ℂ) | MapsTo p univ K} =
        ⋂ t : ℝ≥0, (fun p : C(ℝ≥0, ℂ) => p t) ⁻¹' K := by
      ext p
      simp only [mem_ofPred_eq, MapsTo, mem_univ, forall_const, mem_iInter, mem_preimage]
    rw [he]
    exact isClosed_iInter fun t => hK.preimage (continuous_eval_const t)
  exact hclosed.measurableSet.preimage hf

/-- The successful physical prefix belongs to the actual front past;
failed samples need not have a finite front time. -/
theorem goodRibbonPrefix_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ℱ : Filtration ℝ≥0 mΩ)
    (γ : Ω → ℝ≥0 → ℂ) (ha : Adapted ℱ (fun t ω => γ ω t))
    (hc : ∀ ω, Continuous (γ ω))
    (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime ℱ τ)
    (P : ℂ → ℂ) (he : Topology.IsClosedEmbedding (fun z : closedRibbon => P z)) (ε : ℝ) :
    MeasurableSet[hτ.measurableSpace] (GoodRibbonPrefix γ τ P ε) := by
  let f := fun ω => stoppedAtPath (sourceTracePath γ hc ω) (τ ω)
  have hfm : Measurable[hτ.measurableSpace] f := stoppedAtPath_measurable ℱ γ ha hc τ hτ
  have htm : Measurable[hτ.measurableSpace] (fun ω => (τ ω).untopD 0) := hτ.measurable.untopD 0
  have hem : Measurable[hτ.measurableSpace] (fun ω => f ω ((τ ω).untopD 0)) :=
    continuous_eval.measurable.comp (hfm.prodMk htm)
  let : MeasurableSpace Ω := hτ.measurableSpace
  have hm := (measurableSet_eq_fun hτ.measurable
    (measurable_const : Measurable (fun _ : Ω => (⊤ : WithTop ℝ≥0)))).compl.inter
    ((measurableSet_path_range_closed f hfm _ (ribbonCore_isClosed P he ε)).inter
      ((ribbonCore_isClosed P he (ε / 4)).measurableSet.preimage hem))
  convert hm using 1
  ext ω
  change (τ ω ≠ ⊤ ∧ MapsTo (γ ω) (Icc 0 ((τ ω).untopD 0)) (ribbonCore P ε) ∧
      γ ω ((τ ω).untopD 0) ∈ ribbonCore P (ε / 4)) ↔
    (τ ω ≠ ⊤ ∧ MapsTo (stoppedAtPath (sourceTracePath γ hc ω) (τ ω)) univ (ribbonCore P ε) ∧
      stoppedAtPath (sourceTracePath γ hc ω) (τ ω) ((τ ω).untopD 0) ∈ ribbonCore P (ε / 4))
  cases ht : τ ω with
  | top => simp only [ne_eq, not_true_eq_false, false_and]
  | coe t =>
    simp only [ne_eq, WithTop.coe_ne_top, not_false_eq_true, WithTop.untopD_coe, true_and]
    rw [stoppedAtPath_range_iff]
    have hv := stoppedAtPath_eval_time (sourceTracePath γ hc ω) (t : WithTop ℝ≥0)
    have hv' : stoppedAtPath (sourceTracePath γ hc ω) (t : WithTop ℝ≥0) t = γ ω t := by
      simpa only [WithTop.untopD_coe, sourceTracePath, ContinuousMap.coe_mk] using hv
    rw [hv']
    rfl

lemma RibbonHistory.goodRibbonPrefix
    {C L : ℝ≥0} {ε : ℝ} (d : RibbonHistory C L ε) :
    () ∈ GoodRibbonPrefix (fun _ : Unit => d.trace) (fun _ => (d.time : WithTop ℝ≥0))
      d.chart ε := by
  refine ⟨WithTop.coe_ne_top, ?_, ?_⟩
  · intro t ht
    refine ⟨d.coordinates t, ⟨d.coordinates_ribbon ht, (d.past_core t ht).2⟩, ?_⟩
    exact (d.trace_coordinates ht).symm
  · refine ⟨d.coordinates d.time, ⟨d.coordinates_ribbon ⟨bot_le, le_rfl⟩, ?_⟩, ?_⟩
    · rw [d.attained]
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using d.offset_bound
    · exact (d.trace_coordinates ⟨bot_le, le_rfl⟩).symm

end SLEExactGauge

end

end OAI
