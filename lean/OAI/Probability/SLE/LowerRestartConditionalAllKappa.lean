import Mathlib
import OAI.Probability.SLE.SimplePastMesh

namespace OAI

/-! Lower Restart Conditional All Kappa for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance lowerRestartAllKappaRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance lowerRestartAllKappaComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance lowerRestartAllKappaRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance lowerRestartAllKappaComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_translation_gauge_positive_allKappa (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
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

lemma source_restart_segment_positive_allKappa (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
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
  have htrans := source_translation_gauge_positive_allKappa κ hκ hκ8 h hh hf (U s:ℂ) hL hp
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

lemma RegularSLEPresentation.source_segment_positive_measurable_at_allKappa
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

lemma RegularSLEPresentation.source_segment_null_measurable_at_allKappa
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (h : ℝ → ℝ) (hh : IsGauge h) (s t : ℝ≥0) :
    MeasurableSet[a.filtration t] {ω : a.samples | hausdorffGauge h (γ ω '' Icc s t) = 0} := by
  simpa only [compl_ofPred,not_lt,nonpos_iff_eq_zero] using
    (a.source_segment_positive_measurable_at_allKappa h hh s t).compl

lemma RegularSLEPresentation.source_uniform_null_slot_bound_allKappa
    {Ω : Type} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ p : ℝ≥0∞, 0 < p ∧ p ≤ 1 ∧ ∀ (s δ : ℝ≥0), 0 < δ →
      ∀ A : Set a.samples, MeasurableSet[a.filtration s] A →
        (P.comap Subtype.val) (A ∩ {ω | hausdorffGauge h (γ ω '' Icc s (s+δ)) = 0}) ≤
          (1-p)*(P.comap Subtype.val) A := by
  have hk : 0 < κ := by linarith
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hseed⟩ := sourceUniformInteriorSeed_proved_allKappa κ hκ hκ8 Ω m P inferInstance γ a h hh hf
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
      Measure.map_apply a.source_trace_path_measurable_allKappa hC,
      Measure.restrict_apply (hC.preimage hem)] at he
    change Q (E ∩ A) = Q A * Q {ω | 0 < hausdorffGauge h (K ∩ (γ ω '' Icc 0 δ))} at he
    simpa only [inter_comm] using he
  have hins : (A ∩ {ω | hausdorffGauge h (γ ω '' Icc s (s+δ)) = 0} : Set a.samples) ≤ᵐ[Q] (A \ E : Set a.samples) := by
    filter_upwards [hident] with ω hω
    intro hx
    refine ⟨hx.1,?_⟩
    intro hsuc
    have hpositive := source_restart_segment_positive_allKappa κ hk hκ8 h hh hf
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
lemma RegularSLEPresentation.source_positive_fixed_interval_allKappa
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
    (hf : HasSmallRadiusFormula h (hFormula κ)) (s t : ℝ≥0) (hst : s < t) :
    ∀ᵐ (ω : a.samples) ∂P.comap (Subtype.val : a.samples → Ω), 0 < hausdorffGauge h (γ ω '' Icc s t) := by
  let Q := P.comap (Subtype.val : a.samples → Ω)
  obtain ⟨p,hp,hp1,hslot⟩ := a.source_uniform_null_slot_bound_allKappa hκ hκ8 h hh hf
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
        a.source_segment_null_measurable_at_allKappa h hh s _
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
lemma RegularSLEPresentation.source_positive_all_intervals_allKappa
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (h : ℝ → ℝ) (hh : IsGauge h)
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
    exact a.source_positive_fixed_interval_allKappa hκ hκ8 h hh hf _ _ hrq
  filter_upwards [hrat] with ω hω
  intro s t hs hst
  obtain ⟨r,hsr,hrt⟩ := exists_rat_btwn (show (s:ℝ) < (t:ℝ) from hst)
  obtain ⟨q,hrq,hqt⟩ := exists_rat_btwn hrt
  have hq : 0 < (q:ℝ) := (show 0 < (s:ℝ) from hs).trans (hsr.trans hrq)
  have hp := hω r q ((Real.toNNReal_lt_toNNReal_iff hq).mpr hrq)
  apply hp.trans_le (measure_mono (image_mono (Icc_subset_Icc ?_ ?_)))
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hsr.le
  · simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hqt.le
 

def SourceLowerAllIntervalsTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (γ ω '' Set.Icc s t)
theorem sourceLowerAllIntervals_proved_allKappa : SourceLowerAllIntervalsTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ hSLE h hh hf
  let : IsProbabilityMeasure P := hP
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  have ha := a.source_positive_all_intervals_allKappa hκ hκ8 h hh hf
  rw [←a.measurePreserving_val.map_eq]
  exact (MeasurableEmbedding.subtype_coe a.measurable_samples).ae_map_iff.mpr ha
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge
 

def SourceLowerAllKappaTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (γ ω '' Set.Icc s t)
end SLEExactGauge

namespace SLEExactGauge
theorem sourceLowerAllKappa_proved : SourceLowerAllKappaTarget := sourceLowerAllIntervals_proved_allKappa
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance lowerUniverseRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance lowerUniverseComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance lowerUniverseRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance lowerUniverseComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_lower_universe {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {γ : Ω → ℝ≥0 → ℂ} (hSLE : IsOrdinaryChordalSLE κ γ P)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, 0 < s → s < t →
      0 < hausdorffGauge h (γ ω '' Icc s t) := by
  obtain ⟨a⟩ := exists_regular_sle_presentation hSLE
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let : IsProbabilityMeasure μ := a.probability
  let bp := sourceDriverPath a.B a.continuous_B
  let gp := sourceTracePath (γ ∘ Subtype.val) a.trace_continuous
  have hbm : Measurable bp := source_path_measurable bp a.measurable_B
  have hgm : Measurable gp := source_path_measurable gp (fun t => (hSLE.1 t).comp measurable_subtype_coe)
  let pair : a.samples → C(ℝ≥0,ℝ) × C(ℝ≥0,ℂ) := fun ω => (bp ω, gp ω)
  have hpair : Measurable pair := hbm.prodMk hgm
  let X := range pair
  let f : a.samples → X := fun ω => ⟨pair ω, mem_range_self ω⟩
  have hfm : Measurable f := hpair.subtype_mk
  let Q := μ.map f
  let : IsProbabilityMeasure Q := inferInstance
  let B : ℝ≥0 → X → ℝ := fun t x => x.val.1 t
  let η : X → ℝ≥0 → ℂ := fun x t => x.val.2 t
  have hBm (t : ℝ≥0) : Measurable (B t) :=
    (continuous_eval_const t).measurable.comp (measurable_fst.comp measurable_subtype_coe)
  have hηm (t : ℝ≥0) : Measurable (fun x => η x t) :=
    (continuous_eval_const t).measurable.comp (measurable_snd.comp measurable_subtype_coe)
  have hBrownian : IsBrownianReal B Q := by
    constructor
    · constructor
      intro I
      have hmI : Measurable (fun x : X => I.restrict (B · x)) :=
        Measurable.of_eval (fun index => hBm index)
      refine ⟨hmI.aemeasurable, ?_⟩
      rw [show Q = μ.map f from rfl, Measure.map_map hmI hfm]
      exact (a.brownian.hasLaw I).map_eq
    · exact Eventually.of_forall (fun x => x.val.1.continuous)
  have hη : IsOrdinaryChordalSLE κ η Q := by
    refine ⟨hηm, B, hBrownian, Eventually.of_forall ?_⟩
    intro x
    obtain ⟨ω, hω⟩ := x.property
    refine ⟨a.G ω, a.F ω, ?_⟩
    have hp : pair ω = x.val := hω
    have heB : ∀ t, B t x = a.B t ω := fun t => congrArg (fun z => z.1 t) hp.symm
    have heη : η x = γ ω := by
      exact congrArg (fun z => (z.2 : ℝ≥0 → ℂ)) hp.symm
    simpa only [heB,heη] using a.witness ω
  have hlow := sourceLowerAllKappa_proved κ hκ hκ8 X inferInstance Q inferInstance η hη h hh hf
  have hpull := ae_of_ae_map hfm.aemeasurable hlow
  rw [←a.measurePreserving_val.map_eq]
  apply (MeasurableEmbedding.subtype_coe a.measurable_samples).ae_map_iff.mpr
  exact hpull
end
end SLEExactGauge
end

 
end
end
end

end OAI
