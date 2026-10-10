import OAI.Probability.SLE.Loewner.RawRestartAdaptation

namespace OAI

/-! Reconstruct the old driver through τ+t from its stopped past at τ
and the fresh prefix through t. The reconstruction is jointly measurable
in exactly those two past sigma algebras. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance concatDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance concatDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

def restartDriverPathAt (T : ℝ≥0) (p : C(ℝ≥0,ℝ)) : C(ℝ≥0,ℝ) :=
  ⟨fun s => p (T+s)-p T,
    (p.continuous.comp (continuous_const.add continuous_id)).sub continuous_const⟩

def concatenateDriverPath (T : ℝ≥0) (p q : C(ℝ≥0,ℝ)) : C(ℝ≥0,ℝ) where
  toFun s := if s ≤ T then p s else p T+q (s-T)-q 0
  continuous_toFun := by
    change Continuous ((Iic T).piecewise p (fun s => p T+q (s-T)-q 0))
    apply Continuous.piecewise ?_ p.continuous
      ((continuous_const.add (q.continuous.comp (continuous_id.sub continuous_const))).sub continuous_const)
    intro s hs
    have he : s=T := by simpa only [frontier_Iic,mem_singleton_iff] using hs
    change p s = p T+q (s-T)-q 0
    simp only [he,tsub_self,add_sub_cancel_right]

lemma measurable_concatenateDriverPath :
    Measurable (fun x : ℝ≥0 × (C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ)) =>
      concatenateDriverPath x.1 x.2.1 x.2.2) := by
  apply source_path_measurable
  intro s
  have hp : Measurable (fun x : ℝ≥0 × (C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ)) => x.2.1 s) :=
    (continuous_eval_const s).measurable.comp (measurable_fst.comp measurable_snd)
  have hpT : Measurable (fun x : ℝ≥0 × (C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ)) => x.2.1 x.1) :=
    continuous_eval.measurable.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
  have hq : Measurable (fun x : ℝ≥0 × (C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ)) => x.2.2 (s-x.1)) :=
    continuous_eval.measurable.comp ((measurable_snd.comp measurable_snd).prodMk
      (measurable_const.sub measurable_fst))
  have hq0 : Measurable (fun x : ℝ≥0 × (C(ℝ≥0,ℝ) × C(ℝ≥0,ℝ)) => x.2.2 0) :=
    (continuous_eval_const 0).measurable.comp (measurable_snd.comp measurable_snd)
  exact hp.ite (measurableSet_le measurable_const measurable_fst) ((hpT.add hq).sub hq0)

theorem stoppedDriverPath_concatenation (p : C(ℝ≥0,ℝ)) (T t : ℝ≥0) :
    driverPathStopped (T+t) p = concatenateDriverPath T (driverPathStopped T p)
      (driverPathStopped t (restartDriverPathAt T p)) := by
  ext s
  by_cases hs : s ≤ T
  · have hs' : s ≤ T+t := hs.trans (le_add_of_nonneg_right (show 0 ≤ t from zero_le))
    simp only [driverPathStopped,concatenateDriverPath,ContinuousMap.coe_mk,ite_eq_left hs,
      min_eq_left hs,min_eq_left hs']
  · have hTs : T ≤ s := (lt_of_not_ge hs).le
    have he : T+min (s-T) t=min s (T+t) := by
      rw [add_min,add_tsub_cancel_of_le hTs]
    simp only [driverPathStopped,concatenateDriverPath,restartDriverPathAt,
      ContinuousMap.coe_mk,ite_eq_right hs,min_self,zero_min,add_zero,he]
    ring

lemma restartDriverPathAt_add (p : C(ℝ≥0,ℝ)) (T t : ℝ≥0) :
    restartDriverPathAt t (restartDriverPathAt T p)=restartDriverPathAt (T+t) p := by
  ext s
  change (p (T+(t+s))-p T)-(p (T+t)-p T)=p ((T+t)+s)-p (T+t)
  rw [add_assoc]
  ring

lemma concatenate_stopped_restart (p : C(ℝ≥0,ℝ)) (t : ℝ≥0) :
    concatenateDriverPath t (driverPathStopped t p) (restartDriverPathAt t p)=p := by
  ext s
  by_cases hs : s ≤ t
  · simp only [concatenateDriverPath,driverPathStopped,ContinuousMap.coe_mk,
      ite_eq_left hs,min_eq_left hs]
  · have hts : t ≤ s := (lt_of_not_ge hs).le
    simp only [concatenateDriverPath,driverPathStopped,restartDriverPathAt,ContinuousMap.coe_mk,
      ite_eq_right hs,min_self,add_tsub_cancel_of_le hts,add_zero,sub_self,sub_zero]
    ring

lemma sourceRestartDriverPath_add
    {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    restartDriverPathAt t (sourceRestartDriverPath B hc τ ω)=
      sourceRestartDriverPath B hc (fun ω => τ ω+t) ω :=
  restartDriverPathAt_add (sourceDriverPath B hc ω) (τ ω) t

lemma sourceRestartDriverPath_split
    {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    sourceRestartDriverPath B hc τ ω =
      concatenateDriverPath t (driverPathStopped t (sourceRestartDriverPath B hc τ ω))
        (sourceRestartDriverPath B hc (fun ω => τ ω+t) ω) := by
  rw [←sourceRestartDriverPath_add]
  exact (concatenate_stopped_restart _ _).symm

lemma source_stoppedDriverPath_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace]
      (fun ω => driverPathStopped (τ ω) (sourceDriverPath B hc ω)) := by
  have hprog := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hc
  let : MeasurableSpace Ω := hτ.measurableSpace
  apply source_path_measurable
  intro t
  have hh := (measurable_stoppedValue hprog (hτ.min_const t)).mono
    (IsStoppingTime.measurableSpace_mono (hτ.min_const t) hτ (fun _ => min_le_left _ _)) le_rfl
  change Measurable[hτ.measurableSpace]
    (fun ω => B ((min (τ ω : WithTop ℝ≥0) (t : WithTop ℝ≥0)).untopA) ω) at hh
  change Measurable[hτ.measurableSpace] (fun ω => B (min t (τ ω)) ω)
  simpa only [← WithTop.coe_min,WithTop.untopA,WithTop.untopD_coe,min_comm] using hh

lemma source_stoppedDriverTime_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] τ := by
  convert hτ.measurable.untopA using 1
  funext ω
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]
  rfl

theorem measurable_past_fresh_prefix_concatenation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ ω : WithTop ℝ≥0))) (t : ℝ≥0) :
    Measurable[hτ.measurableSpace.prod (driverPathFiltration t)]
      (fun x : Ω × C(ℝ≥0,ℝ) => concatenateDriverPath (τ x.1)
        (driverPathStopped (τ x.1) (sourceDriverPath B hc x.1)) (driverPathStopped t x.2)) := by
  exact measurable_concatenateDriverPath.comp
    (((source_stoppedDriverTime_measurable τ hτ).comp measurable_fst).prodMk
      (((source_stoppedDriverPath_measurable B hm hc τ hτ).comp measurable_fst).prodMk
        ((driverPathStopped_measurable_past t).comp measurable_snd)))

theorem source_stoppedDriverPath_restart_identity
    {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (fun t => B t ω))
    (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    driverPathStopped (τ ω+t) (sourceDriverPath B hc ω) =
      concatenateDriverPath (τ ω) (driverPathStopped (τ ω) (sourceDriverPath B hc ω))
        (driverPathStopped t (sourceRestartDriverPath B hc τ ω)) := by
  exact stoppedDriverPath_concatenation (sourceDriverPath B hc ω) (τ ω) t

end SLEExactGauge

end

end OAI
