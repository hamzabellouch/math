import Mathlib
import OAI.Probability.SLE.ActualRetainedKernel

namespace OAI

/-! Trace Pos Combined for chordal SLE. -/

section

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_gauge_cost_nonempty (h : ℝ → ℝ) (hh : IsGauge h) (A : Set ℂ) :
    (⨆ _ : A.Nonempty, extendedGauge h (ediam A)) = extendedGauge h (ediam A) := by
  by_cases hA : A.Nonempty
  · simp [hA]
  · rw [Set.not_nonempty_iff_eq_empty.mp hA]
    simp [extendedGauge,hh.zero]

lemma source_gauge_cover_formula (h : ℝ → ℝ) (hh : IsGauge h) (K : Set ℂ) :
    hausdorffGauge h K = ⨆ (r : ℝ≥0∞) (_ : 0 < r),
      ⨅ (U : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, U n) (_ : ∀ n, ediam (U n) ≤ r),
        ∑' n, extendedGauge h (ediam (U n)) := by
  simp only [hausdorffGauge,Measure.mkMetric_apply,source_gauge_cost_nonempty h hh]

lemma source_gauge_open_enlargement (h : ℝ → ℝ) (hh : IsGauge h)
    (A : Set ℂ) (r : ℝ) (hr : (ediam A).toReal < r) (hA : ediam A ≠ ∞)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ U : Set ℂ, IsOpen U ∧ A ⊆ U ∧ ediam U < ENNReal.ofReal r ∧
      extendedGauge h (ediam U) ≤ extendedGauge h (ediam A) + ε := by
  let b (n : ℕ) : ℝ := 1 / ((n:ℝ)+1)
  have hb (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  have hb0 : Tendsto b atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let d := (ediam A).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hlim : Tendsto (fun n => d + 2*b n) atTop (𝓝 d) := by
    simpa only [mul_zero,add_zero] using tendsto_const_nhds.add (hb0.const_mul 2)
  have hhlim : Tendsto (fun n => ENNReal.ofReal (h (d+2*b n))) atTop
      (𝓝 (extendedGauge h (ediam A))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hh.continuousOn d hd).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hlim,Eventually.of_forall (fun n => show 0 ≤ d+2*b n by positivity)⟩))
  have hcost : extendedGauge h (ediam A) < extendedGauge h (ediam A) + ε := by
    exact ENNReal.lt_add_right (by simp [extendedGauge]) (ENNReal.coe_pos.mpr hε).ne'
  obtain ⟨n,hn,hc⟩ := ( (hlim.eventually (gt_mem_nhds hr)).and
    (hhlim.eventually (gt_mem_nhds hcost)) ).exists
  let U := thickening (b n) A
  have hUb : Bornology.IsBounded U := (isBounded_iff_ediam_ne_top.mpr hA).thickening
  have hdiam : (ediam U).toReal ≤ d+2*b n := diam_thickening_le A (hb n).le
  refine ⟨U,isOpen_thickening, self_subset_thickening (hb n) A,?_,?_⟩
  · rw [←ENNReal.ofReal_toReal hUb.ediam_ne_top]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨hdiam.trans_lt hn,by linarith⟩
  · exact (ENNReal.ofReal_le_ofReal (hh.monotoneOn ENNReal.toReal_nonneg
      (show 0 ≤ d+2*b n by positivity) hdiam)).trans hc.le

 
def sourceFiniteOpenCover (h : ℝ → ℝ) (r ε : ℝ≥0∞) (K : Set ℂ) : Prop :=
  ∃ (U : ℕ → Set ℂ) (I : Finset ℕ), (∀ n ∈ I, IsOpen (U n)) ∧
    (∀ n ∈ I, ediam (U n) ≤ r) ∧ K ⊆ ⋃ n ∈ I, U n ∧
    (∑ n ∈ I, extendedGauge h (ediam (U n))) < ε

lemma source_null_compact_finite_open_cover (h : ℝ → ℝ) (hh : IsGauge h)
    (K : Set ℂ) (hK : IsCompact K) (hzero : hausdorffGauge h K = 0)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    sourceFiniteOpenCover h (ENNReal.ofReal r) (ENNReal.ofReal ε) K := by
  have hsmall :
      (⨅ (U : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, U n)
        (_ : ∀ n, ediam (U n) ≤ ENNReal.ofReal (r/2)),
          ∑' n, extendedGauge h (ediam (U n))) < ENNReal.ofReal (ε/2) := by
    apply lt_of_le_of_lt (b := hausdorffGauge h K)
    · rw [source_gauge_cover_formula h hh]
      exact le_iSup_of_le (ENNReal.ofReal (r/2))
        (le_iSup_of_le (ENNReal.ofReal_pos.mpr (by positivity)) le_rfl)
    · simpa only [hzero] using ENNReal.ofReal_pos.mpr (show 0 < ε/2 by positivity)
  obtain ⟨U,hU,hdiam,hcost⟩ := (by simpa only [iInf_lt_iff] using hsmall)
  obtain ⟨e,he,hes⟩ := ENNReal.exists_pos_sum_of_countable
    (ENNReal.ofReal_pos.mpr (show 0 < ε/2 by positivity)).ne' ℕ
  have hfin (n : ℕ) : ediam (U n) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiam n)
  have hrd (n : ℕ) : (ediam (U n)).toReal < r := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdiam n)
    rw [ENNReal.toReal_ofReal (by positivity)] at hb
    linarith
  choose V hopen hUV hVdiam hVcost using fun n =>
    source_gauge_open_enlargement h hh (U n) r (hrd n) (hfin n) (e n) (he n)
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover V hopen (hU.trans (iUnion_mono hUV))
  refine ⟨V,I,fun n _ => hopen n,fun n _ => (hVdiam n).le,hI,?_⟩
  calc
    (∑ n ∈ I, extendedGauge h (ediam (V n))) ≤ ∑' n, extendedGauge h (ediam (V n)) :=
      ENNReal.sum_le_tsum I
    _ ≤ ∑' n, (extendedGauge h (ediam (U n)) + e n) := ENNReal.tsum_le_tsum hVcost
    _ = (∑' n, extendedGauge h (ediam (U n))) + ∑' n, (e n : ℝ≥0∞) := ENNReal.tsum_add
    _ < ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := ENNReal.add_lt_add hcost hes
    _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
end
end SLEExactGauge
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

def sourceFineGaugeContent (h : ℝ → ℝ) (r : ℝ≥0∞) (K : Set ℂ) : ℝ≥0∞ :=
  ⨅ (U : ℕ → Set ℂ) (_ : K ⊆ ⋃ n, U n) (_ : ∀ n, ediam (U n) ≤ r),
    ∑' n, extendedGauge h (ediam (U n))
lemma source_fine_content_finite_cover (h : ℝ → ℝ) (hh : IsGauge h)
    {K : Set ℂ} {R r ε : ℝ≥0∞} (hr : r ≤ R) (hc : sourceFiniteOpenCover h r ε K) :
    sourceFineGaugeContent h R K < ε := by
  classical
  obtain ⟨U,I,hopen,hdiam,hcover,hcost⟩ := hc
  let V (n : ℕ) : Set ℂ := if n ∈ I then U n else ∅
  have hKV : K ⊆ ⋃ n, V n := by
    intro z hz
    obtain ⟨n,hn,hzn⟩ := mem_iUnion₂.mp (hcover hz)
    exact mem_iUnion.mpr ⟨n,by simpa only [V,ite_eq_left hn] using hzn⟩
  have hVdiam (n : ℕ) : ediam (V n) ≤ R := by
    by_cases hn : n ∈ I
    · simpa only [V,ite_eq_left hn] using (hdiam n hn).trans hr
    · simp [V,hn]
  unfold sourceFineGaugeContent
  apply lt_of_le_of_lt (b := ∑' n, extendedGauge h (ediam (V n)))
  · exact iInf_le_of_le V (iInf_le_of_le hKV (iInf_le_of_le hVdiam le_rfl))
  have hsum : (∑' n, extendedGauge h (ediam (V n))) = ∑ n ∈ I, extendedGauge h (ediam (U n)) := by
    rw [tsum_eq_sum (s := I) (fun n hn => by simp [V,hn,extendedGauge,hh.zero])]
    exact Finset.sum_congr rfl (fun n hn => by simp only [V,ite_eq_left hn])
  simpa only [hsum] using hcost

noncomputable def sourceCoverScale (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1/((n:ℝ)+1))
lemma source_coverScale_pos (n : ℕ) : 0 < sourceCoverScale n := by
  unfold sourceCoverScale
  positivity
lemma source_coverScale_tendsto : Tendsto sourceCoverScale atTop (𝓝 0) := by
  unfold sourceCoverScale
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma source_compact_gauge_null_criterion (h : ℝ → ℝ) (hh : IsGauge h)
    (K : Set ℂ) (hK : IsCompact K) :
    hausdorffGauge h K = 0 ↔ ∀ n : ℕ,
      sourceFiniteOpenCover h (sourceCoverScale n) (sourceCoverScale n) K := by
  constructor
  · intro hz n
    exact source_null_compact_finite_open_cover h hh K hK hz _ _ (by positivity) (by positivity)
  · intro hcov
    apply le_antisymm _ zero_le
    rw [source_gauge_cover_formula h hh]
    refine iSup_le fun R => iSup_le fun hR => ?_
    change sourceFineGaugeContent h R K ≤ 0
    apply le_of_tendsto_of_tendsto tendsto_const_nhds source_coverScale_tendsto
    filter_upwards [source_coverScale_tendsto.eventually (gt_mem_nhds hR)] with n hn
    exact (source_fine_content_finite_cover h hh hn.le (hcov n)).le
end
end SLEExactGauge
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance tracePosCoverComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance tracePosCoverComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_finite_open_cover_trace_isOpen (h : ℝ → ℝ) (C : Set ℂ) (hC : IsClosed C)
    (s t : ℝ≥0) (r ε : ℝ≥0∞) :
    IsOpen {γ : C(ℝ≥0,ℂ) | sourceFiniteOpenCover h r ε (C ∩ (γ '' Icc s t))} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro γ hγ
  obtain ⟨U,I,ho,hd,hcov,hcost⟩ := hγ
  let O := ⋃ n ∈ I, U n
  have hO : IsOpen O := isOpen_iUnion (fun n => isOpen_iUnion (fun hn => ho n hn))
  have hmap : MapsTo γ (Icc s t) (Cᶜ ∪ O) := by
    intro u hu
    by_cases hc : γ u ∈ C
    · exact Or.inr (hcov ⟨hc,⟨u,hu,rfl⟩⟩)
    · exact Or.inl hc
  have hev := (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc (hC.isOpen_compl.union hO)).mem_nhds hmap
  filter_upwards [hev] with g hg
  refine ⟨U,I,ho,hd,?_,hcost⟩
  rintro z ⟨hz,u,hu,rfl⟩
  exact (hg hu).resolve_left (fun hn => hn hz)
 

def SourceTracePositiveMeasurableTarget : Prop :=
  ∀ (h : ℝ → ℝ), IsGauge h → ∀ (C : Set ℂ), IsClosed C → ∀ s t : ℝ≥0,
    @MeasurableSet C(ℝ≥0, ℂ) (borel _) {γ | 0 < hausdorffGauge h (C ∩ (γ '' Set.Icc s t))}
theorem sourceTracePositiveMeasurable_proved : SourceTracePositiveMeasurableTarget := by
  intro h hh C hC s t
  have hnull : MeasurableSet {γ : C(ℝ≥0,ℂ) | hausdorffGauge h (C ∩ (γ '' Icc s t)) = 0} := by
    have heq : {γ : C(ℝ≥0,ℂ) | hausdorffGauge h (C ∩ (γ '' Icc s t)) = 0} =
        ⋂ n : ℕ, {γ : C(ℝ≥0,ℂ) | sourceFiniteOpenCover h (sourceCoverScale n) (sourceCoverScale n)
          (C ∩ (γ '' Icc s t))} := by
      ext γ
      simp only [mem_ofPred_eq,mem_iInter]
      exact source_compact_gauge_null_criterion h hh _
        ((isCompact_Icc.image γ.continuous).inter_left hC)
    rw [heq]
    exact MeasurableSet.iInter (fun n =>
      (source_finite_open_cover_trace_isOpen h C hC s t _ _).measurableSet)
  simpa only [compl_ofPred,←ne_eq,←pos_iff_ne_zero] using hnull.compl
end
end SLEExactGauge
end
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance tracePosDilationRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance tracePosDilationComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance tracePosDilationRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance tracePosDilationComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_dilation_gauge_positive (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {c : ℂ} (hc : c ≠ 0) {S : Set ℂ} (hS : IsCompact S)
    (hp : 0 < hausdorffGauge h S) : 0 < hausdorffGauge h ((fun z => c*z) '' S) := by
  by_contra hn
  have hz : hausdorffGauge h ((fun z => c*z) '' S) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have he := source_gauge_holomorphic_compact_null κ hκ hκ8 h hh hf
    (D := univ) (f := fun z => c⁻¹*z) isOpen_univ (hS.image (continuous_const.mul continuous_id))
    (subset_univ _) (by fun_prop) hz
  have hi : (fun z => c⁻¹*z) '' ((fun z => c*z) '' S) = S := by
    rw [←image_comp]
    simp only [Function.comp_def,←mul_assoc,inv_mul_cancel₀ hc,one_mul,image_id']
  change hausdorffGauge h ((fun z => c⁻¹*z) '' ((fun z => c*z) '' S)) = 0 at he
  rw [hi] at he
  exact hp.ne' he

lemma RegularSLEPresentation.source_trace_path_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) :
    Measurable (sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous) := by
  apply source_path_measurable
  intro t
  exact (a.trace_adapted t).mono (a.filtration.le t) le_rfl

lemma RegularSLEPresentation.source_scale_trace_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (c : ℝ≥0) (hc : 0 < c) :
    (P.comap (Subtype.val : a.samples → Ω)).map
      (sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous) =
    (P.comap (Subtype.val : a.samples → Ω)).map
      (sourceTracePath (fun ω : a.samples => sourceScaleTrace c (γ ω))
        (a.sourceScaled c hc).trace_continuous) := by
  exact sourceTraceLawUnique_proved κ hκ hκ8 a.B (a.sourceScaled c hc).B
    a.brownian (a.sourceScaled c hc).brownian a.measurable_B (a.sourceScaled c hc).measurable_B
    a.continuous_B (a.sourceScaled c hc).continuous_B _ _ a.G a.F
    (a.sourceScaled c hc).G (a.sourceScaled c hc).F a.witness (a.sourceScaled c hc).witness
 

def SourceUniformInteriorSeedTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (h : ℝ → ℝ), IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∃ p : ℝ≥0∞, 0 < p ∧ ∀ δ : ℝ≥0, 0 < δ →
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ upperHalfPlane ∧
      p ≤ (P.comap (Subtype.val : a.samples → Ω))
        {ω | 0 < hausdorffGauge h (K ∩ (γ ω '' Set.Icc 0 δ))}
theorem sourceUniformInteriorSeed_proved : SourceUniformInteriorSeedTarget := by
  intro κ hκ hκ8 Ω m P hP γ a h hh hf
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  let z₀ : ℂ := 3*I
  have hz₀ : 2 < z₀.im := by norm_num [z₀]
  obtain ⟨T,E,hT,hE,hp,hseed⟩ :=
    sourceInteriorRetainedTransfer_proved κ hκ hκ8 Ω m P hP γ a z₀ hz₀ h hh hf
  let Q := P.comap (Subtype.val : a.samples → Ω)
  refine ⟨Q E,hp,?_⟩
  intro δ hδ
  let c := NNReal.sqrt (δ/T)
  have hc : 0 < c := by dsimp [c]; exact NNReal.sqrt_pos.mpr (div_pos hδ hT)
  have hc2 : c^2 = δ/T := NNReal.sq_sqrt _
  have ht : sourceScaleTime c δ = T := by
    unfold sourceScaleTime
    rw [hc2]
    field_simp
  let K := (fun z : ℂ => (c:ℂ)*z) '' closedBall z₀ 1
  have hK : IsCompact K := (isCompact_closedBall z₀ 1).image (continuous_const.mul continuous_id)
  have hKH : K ⊆ upperHalfPlane := by
    rintro _ ⟨z,hz,rfl⟩
    have hz' : 0 < z.im := zero_lt_one.trans (source_unit_ball_height hz₀ hz)
    change 0 < ((c:ℂ)*z).im
    simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] using mul_pos (show 0 < (c:ℝ) from hc) hz'
  refine ⟨K,hK,hKH,?_⟩
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let sp := sourceTracePath (fun ω : a.samples => sourceScaleTrace c (γ ω))
    (a.sourceScaled c hc).trace_continuous
  let A : Set C(ℝ≥0,ℂ) := {g | 0 < hausdorffGauge h (K ∩ (g '' Icc 0 δ))}
  have hA : MeasurableSet A := sourceTracePositiveMeasurable_proved h hh K hK.isClosed 0 δ
  have hm : Measurable gp := a.source_trace_path_measurable
  have hsm : Measurable sp := (a.sourceScaled c hc).source_trace_path_measurable
  have hmap := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ A) (a.source_scale_trace_law hk hκ8 c hc)
  rw [Measure.map_apply hm hA,Measure.map_apply hsm hA] at hmap
  change Q E ≤ Q (gp ⁻¹' A)
  rw [hmap]
  apply measure_mono
  intro ω hω
  have hpos := (hseed ω hω).1
  have heq : K ∩ (sourceScaleTrace c (γ ω) '' Icc 0 δ) =
      (fun z : ℂ => (c:ℂ)*z) '' (closedBall z₀ 1 ∩ (γ ω '' Icc 0 T)) := by
    rw [source_scale_past c δ hc,ht, image_inter (mul_right_injective₀ (by exact_mod_cast hc.ne' : (c:ℂ) ≠ 0))]
  change 0 < hausdorffGauge h (K ∩ (sourceScaleTrace c (γ ω) '' Icc 0 δ))
  rw [heq]
  exact source_dilation_gauge_positive κ hk hκ8 h hh hf (by exact_mod_cast hc.ne')
    ((isCompact_closedBall z₀ 1).inter_right (isCompact_Icc.image (a.trace_continuous ω)).isClosed) hpos
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance tracePosRestartRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance tracePosRestartComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance tracePosRestartRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance tracePosRestartComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_translation_gauge_positive (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (b : ℂ) {S : Set ℂ} (hS : IsCompact S)
    (hp : 0 < hausdorffGauge h S) : 0 < hausdorffGauge h ((fun z => z+b) '' S) := by
  by_contra hn
  have hz : hausdorffGauge h ((fun z => z+b) '' S) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have he := source_gauge_holomorphic_compact_null κ hκ hκ8 h hh hf
    (D := univ) (f := fun z => z-b) isOpen_univ (hS.image (continuous_id.add_const b))
    (subset_univ _) (by fun_prop) hz
  have hi : (fun z => z-b) '' ((fun z => z+b) '' S) = S := by
    rw [←image_comp]
    simp only [Function.comp_def,add_sub_cancel_right,image_id']
  change hausdorffGauge h ((fun z => z-b) '' ((fun z => z+b) '' S)) = 0 at he
  rw [hi] at he
  exact hp.ne' he

lemma source_restart_segment_positive (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (s δ : ℝ≥0) (η : C(ℝ≥0,ℂ))
    (hid : ∀ t : ℝ≥0, η t ∈ upperHalfPlane → γ (s+t) = F s (η t + (U s:ℂ)))
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (hp : 0 < hausdorffGauge h (K ∩ (η '' Icc 0 δ))) :
    0 < hausdorffGauge h (γ '' Icc s (s+δ)) := by
  let L := K ∩ (η '' Icc 0 δ)
  have hL : IsCompact L := hK.inter_right (isCompact_Icc.image η.continuous).isClosed
  have hLH : L ⊆ upperHalfPlane := inter_subset_left.trans hKH
  have htrans := source_translation_gauge_positive κ hκ hκ8 h hh hf (U s:ℂ) hL hp
  have htrK : IsCompact ((fun z => z+(U s:ℂ)) '' L) := hL.image (continuous_id.add_const _)
  have htrH : (fun z => z+(U s:ℂ)) '' L ⊆ upperHalfPlane := by
    rintro _ ⟨z,hz,rfl⟩
    simpa only [upperHalfPlane,mem_ofPred_eq,add_im,ofReal_im,add_zero] using hLH hz
  have hpositive := source_inverse_chart_gauge_positive κ hκ hκ8 h hh hf U γ G F hw s htrK htrH htrans
  apply hpositive.trans_le (measure_mono ?_)
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
  obtain ⟨u,hu,rfl⟩ := hz.2
  refine ⟨s+u,⟨le_add_of_nonneg_right hu.1,add_le_add le_rfl hu.2⟩,?_⟩
  exact hid u (hKH hz.1)

lemma RegularSLEPresentation.source_segment_positive_measurable_at
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (h : ℝ → ℝ) (hh : IsGauge h)
    (s t : ℝ≥0) :
    MeasurableSet[a.filtration t] {ω : a.samples | 0 < hausdorffGauge h (γ ω '' Icc s t)} := by
  let f : a.samples → C(ℝ≥0,ℂ) := fun ω =>
    ⟨fun u => γ ω (min u t), (a.trace_continuous ω).comp (continuous_id.min continuous_const)⟩
  have hm : @Measurable a.samples C(ℝ≥0,ℂ) (a.filtration t) (borel _) f := by
    let : MeasurableSpace a.samples := a.filtration t
    apply source_path_measurable
    intro u
    exact (a.trace_adapted (min u t)).mono (a.filtration.mono (min_le_right u t)) le_rfl
  have heq : {ω : a.samples | 0 < hausdorffGauge h (γ ω '' Icc s t)} =
      f ⁻¹' {g : C(ℝ≥0,ℂ) | 0 < hausdorffGauge h (univ ∩ (g '' Icc s t))} := by
    ext ω
    simp only [mem_preimage,mem_ofPred_eq,univ_inter]
    have hi : γ ω '' Icc s t = f ω '' Icc s t := by
      apply image_congr
      intro u hu
      simp only [f,ContinuousMap.coe_mk,min_eq_left hu.2]
    rw [hi]
  rw [heq]
  exact (sourceTracePositiveMeasurable_proved h hh univ isClosed_univ s t).preimage hm

lemma RegularSLEPresentation.source_segment_null_measurable_at
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (h : ℝ → ℝ) (hh : IsGauge h) (s t : ℝ≥0) :
    MeasurableSet[a.filtration t] {ω : a.samples | hausdorffGauge h (γ ω '' Icc s t) = 0} := by
  simpa only [compl_ofPred,not_lt,nonpos_iff_eq_zero] using
    (a.source_segment_positive_measurable_at h hh s t).compl

lemma RegularSLEPresentation.source_uniform_null_slot_bound
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧ ∀ (s δ : ℝ≥0), 0 < δ →
      ∀ A : Set a.samples, MeasurableSet[a.filtration s] A →
        (P.comap Subtype.val) (A ∩ {ω | hausdorffGauge h (γ ω '' Icc s (s+δ)) = 0}) ≤
          (1-p)*(P.comap Subtype.val) A := by
  have hk : 0 < κ := by linarith
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hseed⟩ := sourceUniformInteriorSeed_proved κ hκ hκ8 Ω m P inferInstance γ a h hh hf
  have hp1 : p ≤ 1 := by
    obtain ⟨K,hK,hKH,hKP⟩ := hseed 1 zero_lt_one
    exact hKP.trans (prob_le_one)
  refine ⟨p,hp,hp1,?_⟩
  intro s δ hδ A hA
  obtain ⟨K,hK,hKH,hKP⟩ := hseed δ hδ
  obtain ⟨Φ,hΦm,hΦe,hrestart⟩ := sourceStoppedTraceLaw κ hk hκ8 a.B a.brownian
    a.measurable_B a.continuous_B (fun ω : a.samples => γ ω) a.G a.F a.witness
  let τ : a.samples → ℝ≥0 := fun _ => s
  have hτ : IsStoppingTime a.filtration (fun ω => (τ ω : WithTop ℝ≥0)) := isStoppingTime_const a.filtration s
  have hAstop : MeasurableSet[hτ.measurableSpace] A := by
    change MeasurableSet[(isStoppingTime_const a.filtration s).measurableSpace] A
    rw [IsStoppingTime.measurableSpace_const]
    exact hA
  obtain ⟨hlaw,hident⟩ := hrestart τ hτ
  let rp := sourceRestartDriverPath a.B a.continuous_B τ
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let C : Set C(ℝ≥0,ℂ) := {g | 0 < hausdorffGauge h (K ∩ (g '' Icc 0 δ))}
  let E : Set a.samples := (fun ω => Φ (rp ω)) ⁻¹' C
  have hC : MeasurableSet C := sourceTracePositiveMeasurable_proved h hh K hK.isClosed 0 δ
  have hrm : Measurable rp := by
    apply source_path_measurable
    intro t
    exact (a.measurable_B (s+t)).sub (a.measurable_B s)
  have hem : Measurable (fun ω => Φ (rp ω)) := hΦm.comp hrm
  have hEm : MeasurableSet E := hC.preimage hem
  have hAm : MeasurableSet A := (a.filtration.le s) A hA
  have hprob : Q (A ∩ E) = Q A * Q {ω | 0 < hausdorffGauge h (K ∩ (γ ω '' Icc 0 δ))} := by
    have he := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ C) (hlaw A hAstop)
    rw [Measure.map_apply hem hC,Measure.smul_apply,
      Measure.map_apply a.source_trace_path_measurable hC,
      Measure.restrict_apply (hC.preimage hem)] at he
    change Q (E ∩ A) = Q A * Q {ω | 0 < hausdorffGauge h (K ∩ (γ ω '' Icc 0 δ))} at he
    simpa only [inter_comm] using he
  have hins : (A ∩ {ω | hausdorffGauge h (γ ω '' Icc s (s+δ)) = 0} : Set a.samples) ≤ᵐ[Q] (A \ E : Set a.samples) := by
    filter_upwards [hident] with ω hω
    intro hx
    refine ⟨hx.1,?_⟩
    intro hsuc
    have hpositive := source_restart_segment_positive κ hk hκ8 h hh hf
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (a.F ω) (a.witness ω)
      s δ (Φ (rp ω)) hω hK hKH hsuc
    rw [hx.2] at hpositive
    exact lt_irrefl _ hpositive
  have hdiff : Q (A \ E) = Q A - Q (A ∩ E) := by
    have he : A \ E = A \ (A ∩ E) := by ext ω; simp only [Set.mem_sdiff,mem_inter_iff]; tauto
    rw [he]
    exact measure_sdiff inter_subset_left (hAm.inter hEm).nullMeasurableSet (measure_ne_top Q _)
  calc Q (A ∩ {ω | hausdorffGauge h (γ ω '' Icc s (s+δ)) = 0})
      ≤ Q (A \ E) := measure_mono_ae hins
    _ = Q A - Q (A ∩ E) := hdiff
    _ ≤ Q A - Q A*p := tsub_le_tsub_left (by rw [hprob]; gcongr) _
    _ = (1-p)*Q A := by
      rw [ENNReal.sub_mul (fun _ _ => measure_ne_top Q A),one_mul,mul_comm p (Q A)]
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma RegularSLEPresentation.source_positive_fixed_interval
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ (ω : a.samples) ∂P.comap (Subtype.val : a.samples → Ω), 0 < hausdorffGauge h (γ ω '' Icc s t) := by
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hp1,hslot⟩ := a.source_uniform_null_slot_bound hκ hκ8 h hh hf
  let c : ℝ≥0∞ := 1-p
  have hc : c < 1 := ENNReal.sub_lt_self (by simp) (by simp) hp.ne'
  have hsteps (δ : ℝ≥0) (hδ : 0 < δ) (k : ℕ) :
      Q {ω | hausdorffGauge h (γ ω '' Icc s (s+(k:ℝ≥0)*δ)) = 0} ≤ c^k := by
    induction k with
    | zero => simpa using (prob_le_one (μ := Q)
        (s := {ω | hausdorffGauge h (γ ω '' Icc s (s+(0:ℝ≥0)*δ)) = 0}))
    | succ k ih =>
      have he : s+((k+1:ℕ):ℝ≥0)*δ = (s+(k:ℝ≥0)*δ)+δ := by push_cast; ring
      rw [he,pow_succ,mul_comm (c^k) c]
      let A : Set a.samples := {ω | hausdorffGauge h (γ ω '' Icc s (s+(k:ℝ≥0)*δ)) = 0}
      have hA : MeasurableSet[a.filtration (s+(k:ℝ≥0)*δ)] A :=
        a.source_segment_null_measurable_at h hh s _
      calc Q {ω | hausdorffGauge h (γ ω '' Icc s (s+(k:ℝ≥0)*δ+δ)) = 0}
          ≤ Q (A ∩ {ω | hausdorffGauge h (γ ω '' Icc (s+(k:ℝ≥0)*δ) (s+(k:ℝ≥0)*δ+δ)) = 0}) := by
            apply measure_mono
            intro ω hω
            constructor
            · exact measure_mono_null (image_mono (Icc_subset_Icc le_rfl (le_add_of_nonneg_right (show 0 ≤ δ from bot_le)))) hω
            · exact measure_mono_null (image_mono (Icc_subset_Icc (le_add_of_nonneg_right (by positivity)) le_rfl)) hω
        _ ≤ c * Q A := hslot _ δ hδ A hA
        _ ≤ c * c^k := by gcongr
  have hbound : ∀ᶠ n : ℕ in atTop,
      Q {ω | hausdorffGauge h (γ ω '' Icc s t) = 0} ≤ c^n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < (n:ℝ≥0) := by exact_mod_cast (show 0 < n by omega)
    let δ : ℝ≥0 := (t-s)/(n:ℝ≥0)
    have hδ : 0 < δ := div_pos (tsub_pos_iff_lt.mpr hst) hn0
    have he : s+(n:ℝ≥0)*δ = t := by
      dsimp [δ]
      rw [mul_div_cancel₀ _ hn0.ne',add_tsub_cancel_of_le hst.le]
    simpa only [he] using hsteps δ hδ n
  have hzero : Q {ω | hausdorffGauge h (γ ω '' Icc s t) = 0} = 0 :=
    le_antisymm (ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc) hbound) zero_le
  apply ae_iff.mpr
  simpa only [not_lt,nonpos_iff_eq_zero] using hzero
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma RegularSLEPresentation.source_positive_all_intervals
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 4 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∀ᵐ (ω : a.samples) ∂P.comap (Subtype.val : a.samples → Ω),
      ∀ s t : ℝ≥0, 0 < s → s < t → 0 < hausdorffGauge h (γ ω '' Icc s t) := by
  have hrat : ∀ᵐ (ω : a.samples) ∂P.comap (Subtype.val : a.samples → Ω),
      ∀ r q : ℚ, (r:ℝ).toNNReal < (q:ℝ).toNNReal →
        0 < hausdorffGauge h (γ ω '' Icc (r:ℝ).toNNReal (q:ℝ).toNNReal) := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro hrq
    exact a.source_positive_fixed_interval hκ hκ8 h hh hf _ _ hrq
  filter_upwards [hrat] with ω hω
  intro s t hs hst
  obtain ⟨r,hsr,hrt⟩ := exists_rat_btwn (show (s:ℝ) < (t:ℝ) from hst)
  obtain ⟨q,hrq,hqt⟩ := exists_rat_btwn hrt
  have hq : 0 < (q:ℝ) := (show 0 < (s:ℝ) from hs).trans (hsr.trans hrq)
  have hp := hω r q ((Real.toNNReal_lt_toNNReal_iff hq).mpr hrq)
  apply hp.trans_le (measure_mono (image_mono (Icc_subset_Icc ?_ ?_)))
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hsr.le
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hqt.le
 

def SourceLowerAllIntervalsTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (γ ω '' Set.Icc s t)
theorem sourceLowerAllIntervals_proved : SourceLowerAllIntervalsTarget := by
  intro κ hκ hκ8 Ω m P hP γ hSLE h hh hf
  let : IsProbabilityMeasure P := hP
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  have ha := a.source_positive_all_intervals hκ hκ8 h hh hf
  rw [←a.measurePreserving_val.map_eq]
  exact (MeasurableEmbedding.subtype_coe a.measurable_samples).ae_map_iff.mpr ha
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable def sourceSausageSet (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) (e : ℝ) : Set ℂ :=
  {z | ∃ u ∈ Set.Icc s t, dist z (γ u) < e}
noncomputable def sourceSausageMass (κ : ℝ) (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) (e : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (e^(-codimension κ)) * MeasureTheory.volume (sourceSausageSet γ s t e)
 

def SourceSmallSausageTarget : Prop :=
  ∀ κ : ℝ, 4 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ s t : ℝ≥0, s < t → ∀ ε : ℝ, 0 < ε →
    ∃ a e₀ : ℝ, 0 < a ∧ 0 < e₀ ∧ ∀ e : ℝ, 0 < e → e < e₀ →
      P {ω | sourceSausageMass κ (γ ω) s t e < ENNReal.ofReal a} < ENNReal.ofReal ε
end SLEExactGauge
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
local instance tracePosSausageComplexPathMeasurable : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance tracePosSausageComplexPathBorel : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
lemma source_sausage_isOpen (γ : ℝ≥0 → ℂ) (s t : ℝ≥0) (e : ℝ) :
    IsOpen (sourceSausageSet γ s t e) := by
  have he : sourceSausageSet γ s t e = ⋃ u ∈ Icc s t, ball (γ u) e := by
    ext z; simp [sourceSausageSet]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
lemma source_sausage_joint_open (s t : ℝ≥0) (e : ℝ) :
    IsOpen {p : C(ℝ≥0,ℂ) × ℂ | p.2 ∈ sourceSausageSet p.1 s t e} := by
  have he : {p : C(ℝ≥0,ℂ) × ℂ | p.2 ∈ sourceSausageSet p.1 s t e} =
      ⋃ u ∈ Icc s t, {p : C(ℝ≥0,ℂ) × ℂ | dist p.2 (p.1 u) < e} := by
    ext p; simp [sourceSausageSet]
  rw [he]
  apply isOpen_iUnion; intro u
  apply isOpen_iUnion; intro hu
  exact isOpen_lt (continuous_snd.dist ((continuous_eval_const u).comp continuous_fst)) continuous_const
lemma source_sausage_local_volume_measurable (s t : ℝ≥0) (e : ℝ) (K : Set ℂ) :
    Measurable (fun g : C(ℝ≥0,ℂ) => volume (K ∩ sourceSausageSet g s t e)) := by
  have hm : Measurable (fun p : C(ℝ≥0,ℂ) × ℂ =>
      if p.2 ∈ sourceSausageSet p.1 s t e then (1:ℝ≥0∞) else 0) :=
    Measurable.ite (source_sausage_joint_open s t e).measurableSet measurable_const measurable_const
  have hh := hm.lintegral_prod_right' (ν := volume.restrict K)
  convert hh using 1
  ext g
  change volume (K ∩ sourceSausageSet g s t e) =
    ∫⁻ z, (sourceSausageSet g s t e).indicator (fun _ => 1) z ∂(volume.restrict K)
  rw [lintegral_indicator (source_sausage_isOpen g s t e).measurableSet]
  simp [Measure.restrict_apply (source_sausage_isOpen g s t e).measurableSet,inter_comm]
lemma source_sausage_mass_measurable (κ : ℝ) (s t : ℝ≥0) (e : ℝ) :
    Measurable (fun g : C(ℝ≥0,ℂ) => sourceSausageMass κ g s t e) := by
  exact measurable_const.mul (by simpa only [univ_inter] using source_sausage_local_volume_measurable s t e univ)
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_second_moment_seed {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ≥0∞) (hm : Measurable X)
    (m M : ℝ) (hp : 0 < m) (hM : 0 < M)
    (hfirst : ENNReal.ofReal m ≤ ∫⁻ ω, X ω ∂P)
    (hsecond : (∫⁻ ω, (X ω)^2 ∂P) ≤ ENNReal.ofReal M) :
    ENNReal.ofReal ((m/2)^2/M) ≤ P {ω | ENNReal.ofReal (m/2) ≤ X ω} := by
  classical
  let E := {ω | ENNReal.ofReal (m/2) ≤ X ω}
  have hE : MeasurableSet E := measurableSet_le measurable_const hm
  let Y : Ω → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hYm : Measurable Y := measurable_const.indicator hE
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq P
    (show (2:ℝ).HolderConjugate 2 by constructor <;> norm_num)
    hm.aemeasurable hYm.aemeasurable
  have hYsq : (∫⁻ ω, (Y ω)^(2:ℝ) ∂P) = P E := by
    simp only [Y,Set.indicator_apply]
    simp_rw [show ∀ (b : Prop) [Decidable b], ((if b then 1 else 0):ℝ≥0∞)^(2:ℝ) = if b then 1 else 0 by intros; split_ifs <;> norm_num]
    simpa only [Set.indicator_apply,Pi.one_apply] using (lintegral_indicator_one (μ := P) hE)
  rw [hYsq] at hcs
  simp only [ENNReal.rpow_two] at hcs
  have hcs' : (∫⁻ ω, X ω*Y ω ∂P) ≤ (ENNReal.ofReal M)^(1/(2:ℝ))*(P E)^(1/(2:ℝ)) :=
    hcs.trans (mul_le_mul' (ENNReal.rpow_le_rpow hsecond (by norm_num)) le_rfl)
  have hfirst' : ENNReal.ofReal m ≤ ENNReal.ofReal (m/2) +
      (ENNReal.ofReal M)^(1/(2:ℝ))*(P E)^(1/(2:ℝ)) := by
    apply hfirst.trans
    calc (∫⁻ ω, X ω ∂P) ≤ ∫⁻ ω, ENNReal.ofReal (m/2)+X ω*Y ω ∂P := by
          apply lintegral_mono
          intro ω
          by_cases hω : ω ∈ E
          · simp [Y,hω]
          · have hh : X ω ≤ ENNReal.ofReal (m/2) := (lt_of_not_ge hω).le
            simpa [Y,hω] using hh
      _ = ENNReal.ofReal (m/2)+(∫⁻ ω, X ω*Y ω ∂P) := by
          rw [lintegral_add_left measurable_const]
          simp
      _ ≤ _ := add_le_add le_rfl hcs'
  have hb : ENNReal.ofReal (m/2) +
      (ENNReal.ofReal M)^(1/(2:ℝ))*(P E)^(1/(2:ℝ)) ≠ ⊤ := by finiteness
  have hh := (ENNReal.ofReal_le_iff_le_toReal hb).mp hfirst'
  rw [ENNReal.toReal_add (by simp) (by finiteness),ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_mul,←ENNReal.toReal_rpow,←ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hM.le] at hh
  have hrootM : (M^(1/(2:ℝ)))^2 = M := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hM.le]; norm_num
  have hrootP : ((P E).toReal^(1/(2:ℝ)))^2 = (P E).toReal := by
    rw [←Real.rpow_natCast,←Real.rpow_mul ENNReal.toReal_nonneg]; norm_num
  have hle : (m/2)^2/M ≤ (P E).toReal := by
    apply (div_le_iff₀ hM).mpr
    have hnon : 0 ≤ M^(1/(2:ℝ))*(P E).toReal^(1/(2:ℝ)) := by positivity
    have hs : (m/2)^2 ≤ (M^(1/(2:ℝ))*(P E).toReal^(1/(2:ℝ)))^2 := by nlinarith
    simpa only [mul_pow,hrootM,hrootP,mul_comm] using hs
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P E)).mpr hle
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
omit [IsProbabilityMeasure P] in
lemma source_finite_mass_le_sausage (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 2 < z₀.im) (T : ℝ≥0) {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (ω : a.samples) :
    finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω)
      (e/2) T (closedBall z₀ 1) ≤
    ENNReal.ofReal ((e/2)^(-codimension κ)) *
      volume (closedBall z₀ 1 ∩ sourceSausageSet (γ ω) 0 T e) := by
  have hs : MeasurableSet (sourceSausageSet (γ ω) 0 T e) := (source_sausage_isOpen _ _ _ _).measurableSet
  calc
    _ ≤ ∫⁻ z in closedBall z₀ 1, (sourceSausageSet (γ ω) 0 T e).indicator
        (fun _ => ENNReal.ofReal ((e/2)^(-codimension κ))) z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz'
      by_cases hh : spatialHitTime (γ ω) z (e/2) ≤ T
      · obtain ⟨u,hu,hue⟩ := (spatialHitTime_le_iff (a.trace_continuous ω) z (e/2) T).mp hh
        have hmem : z ∈ sourceSausageSet (γ ω) 0 T e := ⟨u,hu,by rw [dist_comm,hue]; linarith⟩
        simp only [ite_eq_left hh,Set.indicator_of_mem hmem]
        apply ENNReal.ofReal_le_ofReal
        exact ((a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _)
          hκ hκ8 (by positivity) z (by have := source_unit_ball_height hz hz'; linarith)).2
      · simp only [ite_eq_right hh,ENNReal.ofReal_zero,zero_le]
    _ = _ := by
      rw [lintegral_indicator hs,lintegral_const]
      simp [Measure.restrict_apply hs,inter_comm]
lemma source_positive_probability_initial_sausage (hκ : 4 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 2 < z₀.im) :
    ∃ (T : ℝ≥0) (p b e₀ : ℝ), 0 < T ∧ 0 < p ∧ 0 < b ∧ 0 < e₀ ∧
      ∀ e : ℝ, 0 < e → e < e₀ →
        ENNReal.ofReal p ≤ (P.comap (Subtype.val : a.samples → Ω))
          {ω | ENNReal.ofReal b ≤ ENNReal.ofReal (e^(-codimension κ))*
            volume (closedBall z₀ 1 ∩ sourceSausageSet (γ ω) 0 T e)} := by
  have hk : 0 < κ := by linarith
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨T,e₀,m₀,M,hT,he₀,hm₀,hM,hMom⟩ := sourceRetainedSeed_proved κ hκ hκ8 Ω m P inferInstance γ a z₀ hz
  let C := ((1:ℝ)/2)^(-codimension κ)
  have hC : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨T,(m₀/2)^2/M,(m₀/2)/C,min 1 (2*e₀),hT,by positivity,by positivity,lt_min (by norm_num) (by positivity),?_⟩
  intro e he hecut
  let X := fun ω : a.samples => finiteSpatialGreenMass κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (e/2) T (closedBall z₀ 1)
  have hXm : Measurable X := (a.sourceFiniteGreenDensity_measurable (e/2) T).lintegral_prod_right'
  have hhalf : e/2 ≤ e₀ := by have := hecut.trans_le (min_le_right _ _); linarith
  have hXX := hMom (e/2) (by positivity) hhalf
  apply (source_second_moment_seed Q X hXm m₀ M hm₀ hM hXX.1 hXX.2).trans
  apply measure_mono
  intro ω hω
  have hbound := a.source_finite_mass_le_sausage hk hκ8 z₀ hz T he
    (hecut.le.trans (min_le_left _ _)) ω
  have heq : (e/2)^(-codimension κ) = C*e^(-codimension κ) := by
    rw [show e/2 = (1/2)*e by ring,Real.mul_rpow (by norm_num) he.le]
  rw [heq,ENNReal.ofReal_mul hC.le,mul_assoc] at hbound
  have hdiv : ENNReal.ofReal (m₀/2) / ENNReal.ofReal C ≤
      ENNReal.ofReal (e^(-codimension κ))*volume (closedBall z₀ 1 ∩ sourceSausageSet (γ ω) 0 T e) := by
    apply (ENNReal.div_le_iff (by simpa using hC) ENNReal.ofReal_ne_top).mpr
    simpa only [mul_comm] using (hω.trans hbound)
  simpa only [mem_ofPred_eq,ENNReal.ofReal_div_of_pos hC] using hdiv
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_volume_lipschitz_image {f : ℂ → ℂ} {S : Set ℂ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f S) : volume (f '' S) ≤ (L:ℝ≥0∞)^2*volume S := by
  have hhaar : (Measure.hausdorffMeasure (2:ℝ) : Measure ℂ).IsAddHaarMeasure := by
    simpa only [Complex.finrank_real_complex, Nat.cast_ofNat] using
      (inferInstance : (Measure.hausdorffMeasure (Module.finrank ℝ ℂ) : Measure ℂ).IsAddHaarMeasure)
  let _ := hhaar
  have he := Measure.isAddLeftInvariant_eq_smul (Measure.hausdorffMeasure (2:ℝ) : Measure ℂ) volume
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (Measure.hausdorffMeasure (2:ℝ) : Measure ℂ) volume
  have hh := hf.hausdorffMeasure_image_le (d := 2) (by norm_num)
  rw [he,Measure.smul_apply,Measure.smul_apply] at hh
  simp only [ENNReal.smul_def,smul_eq_mul,ENNReal.rpow_two] at hh
  rw [mul_left_comm] at hh
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hc.ne') (by simp)).mp hh
lemma source_holomorphic_compact_lipschitz {f : ℂ → ℂ} {D K : Set ℂ}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) (hf : DifferentiableOn ℂ f D) :
    ∃ L : ℝ≥0, LipschitzOnWith L f K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro x hx
  obtain ⟨L,V,hV,hLip⟩ := (hf.analyticAt (hD.mem_nhds (hKD hx))).contDiffAt.exists_lipschitzOnWith
  exact ⟨L,V,mem_nhdsWithin_of_mem_nhds hV,hLip⟩
lemma source_inverse_chart_compact_bilipschitz
    (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F) (s : ℝ≥0)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane) :
    ∃ L : ℝ≥0, 0 < L ∧ LipschitzOnWith L (F s) K ∧
      ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ (L:ℝ)*dist (F s x) (F s y) := by
  have hFc := hw.2.2.2.2.1 s
  have hGc := hw.2.2.2.1 s
  have hFD : F s '' K ⊆ survivingDomain γ s := by
    rintro _ ⟨z,hz,rfl⟩
    exact hw.2.2.2.2.2.2.1 s (hKH hz)
  obtain ⟨L,hL⟩ := source_holomorphic_compact_lipschitz isOpen_upperHalfPlane hK hKH hFc
  obtain ⟨M,hM⟩ := source_holomorphic_compact_lipschitz (isOpen_survivingDomain hw.1 s)
    (hK.image_of_continuousOn (hFc.continuousOn.mono hKH)) hFD hGc
  refine ⟨max 1 (max L M),lt_of_lt_of_le zero_lt_one (le_max_left _ _),hL.weaken (le_trans (le_max_left _ _) (le_max_right _ _)),?_⟩
  intro x hx y hy
  have hh := hM.dist_le_mul (F s x) ⟨x,hx,rfl⟩ (F s y) ⟨y,hy,rfl⟩
  rw [hw.2.2.2.2.2.2.2.2.1 s x (hKH hx),hw.2.2.2.2.2.2.2.2.1 s y (hKH hy)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (le_trans (le_max_right L M) (le_max_right 1 (max L M)))) dist_nonneg)
end
end SLEExactGauge
end

end OAI
