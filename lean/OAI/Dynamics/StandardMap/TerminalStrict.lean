import OAI.Dynamics.StandardMap.RemainderCap

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical
namespace StandardMapEntropy
noncomputable def fineCap (α:ℝ) (n:ℕ) (z:DyadicTime) (d:NonAffineArray) : ℝ :=
  capF α ((nonaffineHalf^[n]) (nonaffineTranslation z d)).val
lemma measurable_fineCap (α:ℝ) (n:ℕ) (z:DyadicTime) : Measurable (fineCap α n z) :=
  (continuous_capF α).measurable.comp (measurable_subtype_coe.comp ((measurable_nonaffineHalf.iterate n).comp (nonaffineTranslation z).continuous.measurable))
lemma fineCap_zero (α:ℝ) (n:ℕ) (d:NonAffineArray) : fineCap α n 0 d=capF α ((nonaffineHalf^[n]) d).val := by
  have he : nonaffineTranslation 0 d=d := by apply Subtype.ext; exact arrayTranslate_zero d.val
  simp only [fineCap,he]
lemma fineCap_translate (α:ℝ) (n:ℕ) (z:DyadicTime) (d:NonAffineArray) :
    fineCap α n z d=fineCap α n 0 (nonaffineTranslation z d) := by rw [fineCap_zero]; rfl
lemma slow_interval_exists {d:DistanceArray} {c:ℝ} (hu:UnitArray d) (hs:SlowShape (realArray d) c) :
    ∃a b:ℝ,a<b ∧ ∀s t:DyadicTime,(s:ℝ)∈Icc a b → (t:ℝ)∈Icc a b → d.val s t≤c*|(t:ℝ)-(s:ℝ)| := by
  rcases slowShape_dyadic hu hs with h|⟨a,hl,h⟩|⟨b,hr,h⟩|⟨a,b,hab,hl,hr,h⟩
  · exact ⟨0,1,by norm_num,fun s t _ _ => h s t⟩
  · exact ⟨a,a+1,by linarith,fun s t hs ht => h s t hs.1 ht.1⟩
  · exact ⟨b-1,b,by linarith,fun s t hs ht => h s t hs.2 ht.2⟩
  · exact ⟨a,b,hab,h⟩
lemma fineCap_eventually_one (α:ℝ) {d:NonAffineArray} (hu:UnitArray d.val)
    (hs:SlowShape (realArray d.val) (999/1000)) : ∃z:DyadicTime,∀ᶠn:ℕ in atTop,fineCap α n z d=1 := by
  obtain ⟨a,b,hab,hslow⟩ := slow_interval_exists hu hs
  obtain ⟨z,haz,hzb⟩ := dyadic_between hab
  have ht : Tendsto (fun n:ℕ => (1:ℝ)/(2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [one_div,inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num : (2:ℝ)⁻¹<1)
  refine ⟨z,?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.mpr hzb))] with n hn
  unfold fineCap capF
  rw [halfIterate_shortfall n _ (arrayTranslate_unit _ _ hu),dyadicFine_zero]
  change entropyCap α (arrayShortfall 0 (dyadicFine n (dyadicInt 1)) (arrayTranslate z d.val))=1
  rw [shortfall_translate,zero_add]
  apply entropyCap_one
  have hp : 0<(1:ℝ)/(2:ℝ)^n := by positivity
  have he : ((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)=(1:ℝ)/(2:ℝ)^n+(z:ℝ) := by simp only [AddSubgroup.coe_add,dyadicFine_val,dyadicInt_val,Int.cast_one]
  have hb := hslow z (dyadicFine n (dyadicInt 1)+z) ⟨haz.le,hzb.le⟩ (by rw [he]; constructor <;> linarith)
  rw [he,abs_of_pos (by linarith)] at hb
  have hh : d.val.val z (dyadicFine n (dyadicInt 1)+z)/(((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)-(z:ℝ))≤999/1000 := by
    apply (div_le_iff₀ (show 0<((dyadicFine n (dyadicInt 1)+z:DyadicTime):ℝ)-(z:ℝ) by rw [he]; linarith)).mpr
    simpa only [he] using hb
  unfold arrayShortfall
  linarith
noncomputable def fineCapEvent (α:ℝ) (z:DyadicTime) (N:ℕ) : Set NonAffineArray :=
  {d | ∀n≥N,fineCap α n z d=1}
lemma measurableSet_fineCapEvent (α:ℝ) (z:DyadicTime) (N:ℕ) : MeasurableSet (fineCapEvent α z N) := by
  have he : fineCapEvent α z N=⋂n:ℕ,⋂_:N≤n,(fineCap α n z)⁻¹'{1} := by
    ext d; simp only [fineCapEvent,mem_ofPred_eq,mem_iInter,mem_preimage,mem_singleton_iff]
  rw [he]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun _ : N≤n => (measurable_fineCap α n z) (measurableSet_singleton 1)))
lemma fineCapEvent_translate (α:ℝ) (z:DyadicTime) (N:ℕ) :
    fineCapEvent α z N=(nonaffineTranslation z)⁻¹'fineCapEvent α 0 N := by
  ext d
  change (∀n≥N,fineCap α n z d=1) ↔ (∀n≥N,fineCap α n 0 (nonaffineTranslation z d)=1)
  constructor <;> intro h n hn
  · rw [←fineCap_translate]; exact h n hn
  · rw [fineCap_translate]; exact h n hn
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma fineCap_integrable {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) : Integrable (fineCap α n 0) L.terminal := by
  change Integrable (fun d => fineCap α n 0 d) L.terminal
  simp_rw [fineCap_zero]
  exact (integrable_map_measure ((continuous_capF α).measurable.comp measurable_subtype_coe).aestronglyMeasurable
    (measurable_nonaffineHalf.iterate n).aemeasurable).mp (S.backward_cap_integrable L hα hα1 n)
lemma fineCap_integral (α:ℝ) (n:ℕ) : (∫d,fineCap α n 0 d ∂L.terminal)=(∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n) := by
  simp_rw [fineCap_zero]
  exact (integral_map (measurable_nonaffineHalf.iterate n).aemeasurable (show AEStronglyMeasurable (fun d:NonAffineArray => capF α d.val) (S.backwardLaw L n) from ((continuous_capF α).measurable.comp measurable_subtype_coe).aestronglyMeasurable)).symm
lemma terminal_has_positive_event (α:ℝ) (hne:L.terminal≠0) : ∃N:ℕ,0<L.terminal (fineCapEvent α 0 N) := by
  have hc : ∀ᵐd ∂L.terminal,d∈⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N := by
    filter_upwards [S.unit_aeterminal L,S.shape_aeterminal L] with d hu hs
    obtain ⟨z,hz⟩ := fineCap_eventually_one α hu hs
    obtain ⟨N,hN⟩ := eventually_atTop.mp hz
    exact mem_iUnion.mpr ⟨z,mem_iUnion.mpr ⟨N,hN⟩⟩
  by_contra h
  push Not at h
  have hz (z:DyadicTime) (N:ℕ) : L.terminal (fineCapEvent α z N)=0 := by
    rw [fineCapEvent_translate,←Measure.map_apply (nonaffineTranslation z).continuous.measurable (measurableSet_fineCapEvent α 0 N),S.terminal_translate L z]
    exact le_zero_iff.mp (h N)
  have hm : L.terminal (⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N)=0 := measure_iUnion_null (fun z => measure_iUnion_null (hz z))
  have he : L.terminal univ=0 := by
    have hae : (⋃z:DyadicTime,⋃N:ℕ,fineCapEvent α z N)=ᵐ[L.terminal] (univ:Set NonAffineArray) := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hc] with d hd
      exact ⟨fun _ => mem_univ d,fun _ => hd⟩
    rw [←measure_congr hae]
    exact hm
  exact hne (Measure.measure_univ_eq_zero.mp he)

lemma terminal_event_lower {α:ℝ} (hα:0≤α) (hα1:α≤1) (hne:L.terminal≠0) :
    ∃δ:ℝ,0<δ ∧ ∀ᶠn:ℕ in atTop,δ≤∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n := by
  obtain ⟨N,hN⟩ := S.terminal_has_positive_event L α hne
  let E:=fineCapEvent α 0 N
  have hE : MeasurableSet E := measurableSet_fineCapEvent α 0 N
  have he (n:ℕ) (hn:N≤n) : (fineCap α n 0)=ᵐ[L.terminal.restrict E] (fun _ => (1:ℝ)) :=
    (ae_restrict_mem hE).mono (fun d hd => hd n hn)
  have hi : Integrable (fun _:NonAffineArray => (1:ℝ)) (L.terminal.restrict E) :=
    (S.fineCap_integrable L hα hα1 N).restrict.congr (he N le_rfl)
  have : IsFiniteMeasure (L.terminal.restrict E) := (integrable_const_iff_isFiniteMeasure (by norm_num : (1:ℝ)≠0)).mp hi
  have hf : L.terminal E≠∞ := by
    have hh : L.terminal E<∞ := by simpa only [Measure.restrict_apply_univ] using (measure_lt_top (L.terminal.restrict E) univ)
    exact hh.ne
  refine ⟨L.terminal.real E,ENNReal.toReal_pos hN.ne' hf,?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [←S.fineCap_integral L α n]
  have hh := integral_mono_measure (Measure.restrict_le_self : L.terminal.restrict E≤L.terminal)
    (show 0≤ᵐ[L.terminal] fineCap α n 0 from (S.unit_aeterminal L).mono (fun d hd => by
      rw [fineCap_zero,capF]
      exact (entropyCap_bounds hα hα1 (shortfall_unit_mem _ (halfIterate_unit n d hd) _ _ (by norm_num))).1))
    (S.fineCap_integrable L hα hα1 n)
  rw [integral_congr_ae (he n hn),integral_const] at hh
  simpa only [smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] using hh
lemma capG_backward_partial {α:ℝ} (hα:0≤α) (hα1:α≤1) (n:ℕ) :
    (∑j∈Finset.range n,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))=
      (∫d:NonAffineArray,capF α d.val ∂L.terminal)-(∫d:NonAffineArray,capF α d.val ∂S.backwardLaw L n) := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,S.backwardLaw_zero L,sub_self]
  | succ n ih => rw [Finset.sum_range_succ,ih,S.backward_cap_difference L hα hα1 n]; ring
lemma terminal_cap_strict {α H:ℝ} (hα:0≤α) (hα1:α≤1) (hH:0<H)
    (hb:(∫d:NonAffineArray,capF α d.val ∂L.terminal)≤H) :
    (∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))<H := by
  by_cases hn:L.terminal=0
  · simpa only [backwardLaw,hn,Measure.map_zero,integral_zero_measure,tsum_zero] using hH
  obtain ⟨δ,hδ,hd⟩ := S.terminal_event_lower L hα hα1 hn
  have hs := (hasSum_integral_measure (S.capG_integrable_sum L α)).summable
  have ht := hs.hasSum.tendsto_sum_nat
  have hle : (∑'j:ℕ,∫d:NonAffineArray,capG α d.val ∂S.backwardLaw L (j+1))≤
      (∫d:NonAffineArray,capF α d.val ∂L.terminal)-δ := by
    apply le_of_tendsto ht
    filter_upwards [hd] with n hn
    rw [S.capG_backward_partial L hα hα1 n]
    linarith
  linarith
end CriticalScaleSequence
end StandardMapEntropy

end OAI
