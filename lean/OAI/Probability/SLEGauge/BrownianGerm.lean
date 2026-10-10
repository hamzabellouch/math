import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.FutureSupport

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.BrownianGerm

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

 
@[instance_reducible] def future (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω u => B (t+u) ω - B t ω) inferInstance

omit mΩ in
lemma measurable_shift (B : ℝ≥0 → Ω → ℝ) (s u : ℝ≥0) :
    Measurable[future B s] (fun ω => B (s+u) ω-B s ω) :=
  (measurable_pi_apply u).comp
    (comap_measurable (fun ω v => B (s+v) ω-B s ω))

lemma future_le (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t)) (t : ℝ≥0) :
    future B t ≤ mΩ :=
  (Measurable.of_eval fun offset => (hm (t + offset)).sub (hm t)).comap_le

omit mΩ in
lemma future_antitone (B : ℝ≥0 → Ω → ℝ) : Antitone (future B) := by
  intro s t hst
  suffices Measurable[future B s] (fun ω u => B (t+u) ω - B t ω) from
    this.comap_le
  let : MeasurableSpace Ω := future B s
  refine Measurable.of_eval fun u => ?_
  have h := (measurable_shift B s (t-s+u)).sub (measurable_shift B s (t-s))
  convert h using 1; ext ω
  simp only [← add_assoc, add_tsub_cancel_of_le hst, Pi.sub_apply]
  ring

 

omit mΩ in
lemma measurable_eval_iSup_future (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hz : ∀ ω, B 0 ω=0) (t : ℝ≥0) :
    Measurable[⨆ s : {s : ℝ≥0 // 0<s}, future B s.1] (B t) := by
  let ε : ℕ → ℝ≥0 := fun n => ((n:ℝ≥0)+1)⁻¹
  have hep (n : ℕ) : 0<ε n := by dsimp [ε]; positivity
  have he : Tendsto ε atTop (𝓝 0) := by
    simpa [ε,one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/((n:ℝ≥0)+1)) atTop (𝓝 0))
  let : MeasurableSpace Ω := ⨆ s : {s : ℝ≥0 // 0<s}, future B s.1
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => B (ε n+t) ω-B (ε n) ω)
  · intro n
    exact (measurable_shift B (ε n) t).mono (le_iSup_of_le ⟨ε n,hep n⟩ le_rfl) le_rfl
  · apply tendsto_pi_nhds.mpr
    intro ω
    have h := ((hc ω).tendsto (0+t)).comp (he.add_const t)
    have h' := ((hc ω).tendsto 0).comp he
    simpa [hz ω] using h.sub h'

 

theorem measure_zero_or_one (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, StronglyMeasurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hz : ∀ ω, B 0 ω=0)
    (P : Measure Ω) (hB : IsPreBrownianReal B P)
    {E : Set Ω}
    (hE : ∀ t : ℝ≥0, 0<t → MeasurableSet[Filtration.natural B hm t] E) :
    P E=0 ∨ P E=1 := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let g : MeasurableSpace Ω := ⨅ t : {t : ℝ≥0 // 0<t}, Filtration.natural B hm t.1
  let f : {t : ℝ≥0 // 0<t} → MeasurableSpace Ω := fun t => future B t.1
  have hg1 : g ≤ Filtration.natural B hm 1 :=
    iInf_le (fun t : {t : ℝ≥0 // 0<t} => Filtration.natural B hm t.1) ⟨1,by norm_num⟩
  have hg : g ≤ mΩ := hg1.trans ((Filtration.natural B hm).le 1)
  have hi (t : {t : ℝ≥0 // 0<t}) : Indep (f t) g P := by
    have h := (IndepFun_iff_Indep _ _ _).mp (hB.indepFun_shift t.1)
    rw [← Filtration.natural_eq_comap B hm t.1] at h
    exact indep_of_indep_of_le_right h (iInf_le _ t)
  have hd : Directed (· ≤ ·) f := by
    intro s t
    refine ⟨⟨min s.1 t.1,lt_min s.2 t.2⟩, ?_, ?_⟩
    · exact future_antitone B (min_le_left _ _)
    · exact future_antitone B (min_le_right _ _)
  have hind : Indep (⨆ t, f t) g P :=
    indep_iSup_of_directed_le hi (fun t => @future_le Ω mΩ B (fun u => (hm u).measurable) t.1) hg hd
  have hgE : MeasurableSet[g] E := by
    exact (MeasurableSpace.measurableSet_iInf).mpr fun t => hE t.1 t.2
  have hng : Filtration.natural B hm 1 ≤ ⨆ t, f t := by
    rw [Filtration.natural_eq_comap]
    let : MeasurableSpace Ω := ⨆ t, f t
    exact (Measurable.of_eval fun t : Iic (1:ℝ≥0) =>
      measurable_eval_iSup_future B hc hz t.1).comap_le
  exact measure_eq_zero_or_one_of_indepSet_self
    (hind.indepSet_of_measurableSet (hng _ (hE 1 (by norm_num))) hgE)

 

lemma measurableSet_limsup_germ
    (ℱ : Filtration ℝ≥0 mΩ) (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0))
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet[ℱ (τ n)] (E n))
    (t : ℝ≥0) (ht : 0<t) : MeasurableSet[ℱ t] (limsup E atTop) := by
  classical
  have hev : ∀ᶠ n in atTop, τ n≤t :=
    (hτ.eventually (gt_mem_nhds ht)).mono (fun _ h => h.le)
  have heq : E =ᶠ[atTop] (fun n => if τ n≤t then E n else ∅) :=
    hev.mono fun n hn => by simp [hn]
  rw [limsup_congr heq]
  let : MeasurableSpace Ω := ℱ t
  apply MeasurableSet.measurableSet_limsup
  intro n
  split_ifs with h
  · exact ℱ.mono h _ (hE n)
  · exact MeasurableSet.empty

 
theorem measure_zero_or_one_limsup (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, StronglyMeasurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hz : ∀ ω, B 0 ω=0)
    (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0))
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet[Filtration.natural B hm (τ n)] (E n)) :
    P (limsup E atTop)=0 ∨ P (limsup E atTop)=1 :=
  measure_zero_or_one B hm hc hz P hB
    (measurableSet_limsup_germ (Filtration.natural B hm) τ hτ E hE)

end SLEExactGauge.BrownianGerm
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.GermPositivity
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
lemma mem_limsup_iff_mem_iInter {E : ℕ → Set Ω} {ω : Ω}
    (hE : Antitone (fun n => ω ∈ E n)) :
    ω ∈ limsup E atTop ↔ ω ∈ ⋂ n, E n := by
  rw [mem_limsup_iff_frequently_mem,mem_iInter]
  constructor
  · intro h n
    obtain ⟨m,hm,hmem⟩ := frequently_atTop.mp h n
    exact hE hm hmem
  · exact fun h => Filter.Frequently.of_forall h

 

lemma limsup_ae_eq_iInter {P : Measure Ω} {E : ℕ → Set Ω}
    (hE : ∀ᵐ ω ∂P, Antitone (fun n => ω ∈ E n)) :
    ∀ᵐ ω ∂P, ω ∈ limsup E atTop ↔ ω ∈ ⋂ n, E n := by
  exact hE.mono fun _ h => mem_limsup_iff_mem_iInter h

 

theorem ae_all_mem (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, StronglyMeasurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hz : ∀ ω, B 0 ω=0)
    (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0))
    (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet[Filtration.natural B hm (τ n)] (E n))
    (hanti : ∀ᵐ ω ∂P, Antitone (fun n => ω ∈ E n))
    {p : ℝ≥0∞} (hp : 0<p) (hlower : ∀ n, p≤P (E n)) :
    ∀ᵐ ω ∂P, ∀ n, ω ∈ E n := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have he (n : ℕ) : MeasurableSet (E n) :=
    (Filtration.natural B hm).le (τ n) _ (hE n)
  have hmI : MeasurableSet (⋂ n, E n) := MeasurableSet.iInter he
  have hprob : p≤P (⋂ n, E n) := by
    rw [measure_iInter_of_ae_antitone hanti (fun n => (he n).nullMeasurableSet)
      ⟨0,measure_ne_top _ _⟩]
    exact le_iInf hlower
  have hEq : P (limsup E atTop)=P (⋂ n, E n) :=
    measure_congr (eventuallyEqSet_iff.mpr (limsup_ae_eq_iInter hanti))
  have hpos : 0<P (limsup E atTop) := by rw [hEq]; exact hp.trans_le hprob
  have hz1 := BrownianGerm.measure_zero_or_one_limsup B hm hc hz P hB τ hτ E hE
  have hone : P (limsup E atTop)=1 := hz1.resolve_left (ne_of_gt hpos)
  have hi : ∀ᵐ ω ∂P, ω ∈ ⋂ n, E n := by
    apply (ae_iff_measure_eq hmI.nullMeasurableSet).mpr
    rw [measure_univ]
    convert! hEq.symm.trans hone using 1
  simpa only [mem_iInter] using hi

 
def smallTime (n : ℕ) : ℝ≥0 := ((n:ℝ≥0)+1)⁻¹

lemma smallTime_pos (n : ℕ) : 0<smallTime n := by dsimp [smallTime]; positivity

lemma smallTime_antitone : Antitone smallTime := by
  intro n m hnm
  dsimp [smallTime]
  apply inv_anti₀ (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 1

lemma tendsto_smallTime : Tendsto smallTime atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n:ℝ≥0)+1)⁻¹) atTop (𝓝 0)
  simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1/((n:ℝ≥0)+1)) atTop (𝓝 0))

 

theorem ae_positive_all_times (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, StronglyMeasurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hz : ∀ ω, B 0 ω=0)
    (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (A : ℝ≥0 → Ω → ℝ≥0∞)
    (hAm : ∀ t, Measurable[Filtration.natural B hm t] (A t))
    (hAo : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    {p : ℝ≥0∞} (hp : 0<p)
    (hlower : ∀ t : ℝ≥0, 0<t → p≤P {ω | 0<A t ω}) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0<t → 0<A t ω := by
  let E (n : ℕ) : Set Ω := {ω | 0<A (smallTime n) ω}
  have hEm (n : ℕ) : MeasurableSet[Filtration.natural B hm (smallTime n)] (E n) :=
    measurableSet_lt measurable_const (hAm _)
  have hant : ∀ᵐ ω ∂P, Antitone (fun n => ω∈E n) := by
    filter_upwards [hAo] with ω hω n m hnm hmem
    exact hmem.trans_le (hω (smallTime_antitone hnm))
  have hs := ae_all_mem B hm hc hz P hB smallTime tendsto_smallTime E hEm hant hp
    (fun n => hlower _ (smallTime_pos n))
  filter_upwards [hs,hAo] with ω hsω hoω t ht
  obtain ⟨n,hn⟩ := (tendsto_smallTime.eventually (gt_mem_nhds ht)).exists
  exact (hsω n).trans_le (hoω hn.le)

 

theorem ae_positive_all_times_of_same_probability (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, StronglyMeasurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hz : ∀ ω, B 0 ω=0)
    (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (A : ℝ≥0 → Ω → ℝ≥0∞)
    (hAm : ∀ t, Measurable[Filtration.natural B hm t] (A t))
    (hAo : ∀ᵐ ω ∂P, Monotone (fun t => A t ω))
    (hpos : ∃ u : ℝ≥0, 0<u ∧ 0<P {ω | 0<A u ω})
    (heq : ∀ s t : ℝ≥0, 0<s → 0<t → P {ω | 0<A s ω}=P {ω | 0<A t ω}) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0<t → 0<A t ω := by
  obtain ⟨u,hu,hp⟩ := hpos
  exact ae_positive_all_times B hm hc hz P hB A hAm hAo hp
    (fun t ht => (heq u t hu ht).le)

end SLEExactGauge.GermPositivity
end
end
 

 
section
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma physicalGreen_split_bound (a : ℝ) (ha : 1/4 < a) (R : ℝ) (hR : 0 < R)
    (v : State) (hv : 0 < Y v) :
    physicalGreen a v ≤ (physicalGreen a v * lifetimeTest (lifetimeExponent a) v) /
      R ^ (lifetimeExponent a / 2) +
      (R / (lifetimeDrift a * R ^ (lifetimeExponent a / 2))) * lifetimeCost a v := by
  let q := lifetimeExponent a
  let c := lifetimeDrift a
  have hq : 0 < q := lifetimeExponent_pos ha
  have hc : 0 < c := lifetimeDrift_pos ha
  have hp : 0 < R ^ (q/2) := Real.rpow_pos_of_pos hR _
  have hG : 0 < physicalGreen a v := Real.exp_pos _
  have hF : 0 ≤ physicalGreen a v * lifetimeTest q v :=
    mul_nonneg hG.le (lifetimeTest_nonneg q v hv.le)
  have hC : 0 ≤ R / (c * R^(q/2)) * lifetimeCost a v := by
    exact mul_nonneg (by positivity) (lifetimeCost_pos ha hv).le
  change physicalGreen a v ≤ _ / R^(q/2) + (R/(c*R^(q/2))) * lifetimeCost a v
  by_cases hs : R ≤ Q v
  · have ht : R^(q/2) ≤ lifetimeTest q v :=
      (Real.rpow_le_rpow hR.le hs (by positivity)).trans (lifetimeTest_coercive q v hv.le)
    have h := mul_le_mul_of_nonneg_left ht hG.le
    exact ((le_div_iff₀ hp).mpr h).trans (le_add_of_nonneg_right hC)
  · have heq : R^(q/2-1) = R^(q/2)/R := by
      rw [Real.rpow_sub hR,Real.rpow_one]
    have he : R^(q/2)/R ≤ Q v^(q/2-1) := by
      rw [← heq]
      apply Real.rpow_le_rpow_of_nonpos (Q_pos hv) (le_of_not_ge hs)
      have hq1 := lifetimeExponent_le_one a
      dsimp only [q]
      linarith
    have hprod := mul_le_mul_of_nonneg_left he
      (show 0 ≤ R / (c * R^(q/2)) * (c * physicalGreen a v) by positivity)
    have hcancel : R / (c * R^(q/2)) * (c * physicalGreen a v) * (R^(q/2)/R) =
        physicalGreen a v := by field_simp
    rw [hcancel] at hprod
    have hb : physicalGreen a v ≤ (R/(c*R^(q/2))) * lifetimeCost a v := by
      convert hprod using 1; first | rfl | (dsimp [lifetimeCost,c,q]; ring)
    exact hb.trans (le_add_of_nonneg_left (div_nonneg hF hp.le))

lemma killedGreen_split_bound (a : ℝ) (ha : 1/4 < a) (R : ℝ) (hR : 0 < R)
    (z : UpperPlane) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) :
    killedObservable a z (physicalGreen a) t b ≤
      killedObservable a z (fun v => physicalGreen a v * lifetimeTest (lifetimeExponent a) v)
        t b / R^(lifetimeExponent a/2) +
      (R / (lifetimeDrift a * R^(lifetimeExponent a/2))) *
        killedObservable a z (lifetimeCost a) t b := by
  unfold killedObservable
  split_ifs with ht
  · apply physicalGreen_split_bound a ha R hR
    obtain ⟨f,hf⟩ := ht
    have he : loewnerMap a b.1 t z.1 = f t := by
      simpa only [Real.toNNReal_coe] using
        loewnerMap_eq_solution_time hf (right_mem_Icc.mpr t.coe_nonneg)
    simpa only [actualState,Y_apply,he,Complex.sub_im,Complex.ofReal_im,sub_zero] using
      (hf.2 (t : ℝ) (right_mem_Icc.mpr t.coe_nonneg)).1
  · simp only [zero_div,mul_zero,add_zero,le_refl]

lemma killedObservable_real_joint_measurable (a : ℝ) (z : UpperPlane)
    (F : State → ℝ) (hF : Measurable F) :
    Measurable (fun p : ℝ × ExactSLEGenerator.Driver =>
      ENNReal.ofReal (killedObservable a z F p.1.toNNReal p.2)) :=
  ((killedObservable_joint_measurable a z F hF).comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal

lemma killedGreen_timeIntegral_bound (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (R : ℝ) (hR : 0 < R) (T : ℝ≥0) :
    (∫⁻ u in Ioc (0 : ℝ) (T : ℝ), ∫⁻ b,
      ENNReal.ofReal (killedObservable a z (physicalGreen a) u.toNNReal b) ∂W) ≤
    ENNReal.ofReal (((T : ℝ) / R^(lifetimeExponent a/2) +
      R / (lifetimeDrift a * R^(lifetimeExponent a/2))) *
      (physicalGreen a (z.1,0) * lifetimeTest (lifetimeExponent a) (z.1,0))) := by
  let q := lifetimeExponent a
  let c := lifetimeDrift a
  let M := physicalGreen a (z.1,0) * lifetimeTest q (z.1,0)
  let A : ℝ := 1 / R^(q/2)
  let B : ℝ := R / (c*R^(q/2))
  let F : ℝ → ExactSLEGenerator.Driver → ℝ≥0∞ := fun u b => ENNReal.ofReal
    (killedObservable a z (fun v => physicalGreen a v * lifetimeTest q v) u.toNNReal b)
  let C : ℝ → ExactSLEGenerator.Driver → ℝ≥0∞ := fun u b => ENNReal.ofReal
    (killedObservable a z (lifetimeCost a) u.toNNReal b)
  have hM : 0 ≤ M := mul_nonneg (Real.exp_pos _).le (lifetimeTest_nonneg q _ z.2.le)
  have hc : 0 < c := lifetimeDrift_pos ha
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFm : Measurable (Function.uncurry F) :=
    killedObservable_real_joint_measurable a z _ (greenLifetime_measurable a)
  have hCm : Measurable (Function.uncurry C) :=
    killedObservable_real_joint_measurable a z _ (lifetimeCost_measurable a)
  have hFu (u : ℝ) : Measurable (F u) :=
    hFm.comp (measurable_const.prodMk measurable_id)
  have hCu (u : ℝ) : Measurable (C u) :=
    hCm.comp (measurable_const.prodMk measurable_id)
  have hFim : Measurable (fun u => ∫⁻ b, F u b ∂W) := hFm.lintegral_prod_right
  have hCim : Measurable (fun u => ∫⁻ b, C u b ∂W) := hCm.lintegral_prod_right
  have hFub (u : ℝ) : (∫⁻ b, F u b ∂W) ≤ ENNReal.ofReal M :=
    global_lifetime_test_budget a ha W hW z u.toNNReal
  have hFint : (∫⁻ u in Ioc (0 : ℝ) (T : ℝ), ∫⁻ b, F u b ∂W) ≤
      ENNReal.ofReal M * ENNReal.ofReal (T : ℝ) := by
    calc
      _ ≤ ∫⁻ _u in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal M := lintegral_mono hFub
      _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc,sub_zero]
  have hCint : (∫⁻ u in Ioc (0 : ℝ) (T : ℝ), ∫⁻ b, C u b ∂W) ≤ ENNReal.ofReal M := by
    rw [lintegral_lintegral_swap hCm.aemeasurable]
    apply le_trans (lintegral_mono (fun b => lintegral_mono_set Ioc_subset_Ioi_self))
    exact global_lifetime_occupation_budget a ha W hW z
  have hsplit (u : ℝ) (b : ExactSLEGenerator.Driver) :
      ENNReal.ofReal (killedObservable a z (physicalGreen a) u.toNNReal b) ≤
        ENNReal.ofReal A * F u b + ENNReal.ofReal B * C u b := by
    have hFn := killedObservable_nonneg a z
      (fun v => physicalGreen a v * lifetimeTest q v)
      (fun v hv => mul_nonneg (Real.exp_pos _).le (lifetimeTest_nonneg q v hv.le)) u.toNNReal b
    have hCn := killedObservable_nonneg a z (lifetimeCost a)
      (fun v hv => (lifetimeCost_pos ha hv).le) u.toNNReal b
    have h := ENNReal.ofReal_le_ofReal (killedGreen_split_bound a ha R hR z u.toNNReal b)
    have he : killedObservable a z
        (fun v => physicalGreen a v * lifetimeTest q v) u.toNNReal b / R^(q/2) =
        A * killedObservable a z
          (fun v => physicalGreen a v * lifetimeTest q v) u.toNNReal b := by dsimp [A]; ring
    change _ ≤ ENNReal.ofReal (_ / R^(q/2) + B * _) at h
    rw [he, ENNReal.ofReal_add (mul_nonneg hA hFn) (mul_nonneg hB hCn),
      ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB] at h
    exact h
  have hsplitInt (u : ℝ) :
      (∫⁻ b, ENNReal.ofReal (killedObservable a z (physicalGreen a) u.toNNReal b) ∂W) ≤
        ENNReal.ofReal A * (∫⁻ b, F u b ∂W) + ENNReal.ofReal B * (∫⁻ b, C u b ∂W) := by
    calc
      _ ≤ ∫⁻ b, ENNReal.ofReal A * F u b + ENNReal.ofReal B * C u b ∂W :=
        lintegral_mono (hsplit u)
      _ = _ := by rw [lintegral_add_left ((hFu u).const_mul (ENNReal.ofReal A)),
          lintegral_const_mul _ (hFu u), lintegral_const_mul _ (hCu u)]
  calc
    _ ≤ ∫⁻ u in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal A * (∫⁻ b, F u b ∂W) + ENNReal.ofReal B * (∫⁻ b, C u b ∂W) :=
      lintegral_mono hsplitInt
    _ = ENNReal.ofReal A * (∫⁻ u in Ioc (0 : ℝ) (T : ℝ), ∫⁻ b, F u b ∂W) +
        ENNReal.ofReal B * (∫⁻ u in Ioc (0 : ℝ) (T : ℝ), ∫⁻ b, C u b ∂W) := by
      rw [lintegral_add_left (hFim.const_mul (ENNReal.ofReal A)),
        lintegral_const_mul _ hFim, lintegral_const_mul _ hCim]
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal M * ENNReal.ofReal (T : ℝ)) +
        ENNReal.ofReal B * ENNReal.ofReal M :=
      add_le_add (mul_le_mul_right hFint _) (mul_le_mul_right hCint _)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hM, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB,
        ← ENNReal.ofReal_add (mul_nonneg hA (mul_nonneg hM T.coe_nonneg)) (mul_nonneg hB hM)]
      congr 1
      dsimp [A,B,M,q,c]
      ring

 

theorem killedGreen_polynomial_decay (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (T : ℝ≥0) (hT : 0 < T) :
    (∫ b, killedObservable a z (physicalGreen a) T b ∂W) ≤
      (1 + 1 / lifetimeDrift a) *
        (physicalGreen a (z.1,0) * lifetimeTest (lifetimeExponent a) (z.1,0)) /
        (T : ℝ)^(lifetimeExponent a/2) := by
  have ht : 0 < (T : ℝ) := hT
  have htime := killedGreen_timeIntegral_bound a ha W hW z T ht T
  have hlower : ENNReal.ofReal (T : ℝ) *
      (∫⁻ b, ENNReal.ofReal (killedObservable a z (physicalGreen a) T b) ∂W) ≤
      ∫⁻ u in Ioc (0 : ℝ) (T : ℝ), ∫⁻ b,
        ENNReal.ofReal (killedObservable a z (physicalGreen a) u.toNNReal b) ∂W := by
    calc
      _ = ∫⁻ _u in Ioc (0 : ℝ) (T : ℝ), ∫⁻ b,
          ENNReal.ofReal (killedObservable a z (physicalGreen a) T b) ∂W := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc,sub_zero,mul_comm]
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        apply killedGreen_lintegral_antitone a ha W hW z
        simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hu.2
  have HB := hlower.trans htime
  rw [← ofReal_integral_eq_lintegral_ofReal (killedGreen_integrable a ha W hW z T)
      (Eventually.of_forall (killedGreen_nonneg a z T)),
    ← ENNReal.ofReal_mul ht.le] at HB
  have hp : 0 < (T : ℝ)^(lifetimeExponent a/2) := Real.rpow_pos_of_pos ht _
  have hc : 0 < lifetimeDrift a := lifetimeDrift_pos ha
  have hM : 0 ≤ physicalGreen a (z.1,0) * lifetimeTest (lifetimeExponent a) (z.1,0) :=
    mul_nonneg (Real.exp_pos _).le (lifetimeTest_nonneg _ _ z.2.le)
  have HR := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp HB
  have he : ((T : ℝ)/(T : ℝ)^(lifetimeExponent a/2) +
      (T : ℝ)/(lifetimeDrift a*(T : ℝ)^(lifetimeExponent a/2))) *
      (physicalGreen a (z.1,0)*lifetimeTest (lifetimeExponent a) (z.1,0)) =
      (T : ℝ) * ((1+1/lifetimeDrift a) *
        (physicalGreen a (z.1,0)*lifetimeTest (lifetimeExponent a) (z.1,0)) /
        (T : ℝ)^(lifetimeExponent a/2)) := by ring
  rw [he] at HR
  exact (mul_le_mul_iff_right₀ ht).mp HR

 

theorem killedGreen_mean_tendsto_zero (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) :
    Tendsto (fun T : ℝ≥0 => ∫ b, killedObservable a z (physicalGreen a) T b ∂W)
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun T => integral_nonneg (killedGreen_nonneg a z T)))
  · filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with T hT
    exact killedGreen_polynomial_decay a ha W hW z T hT
  · exact tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop (by linarith [lifetimeExponent_pos ha] : 0 < lifetimeExponent a/2)).comp
        (NNReal.tendsto_coe_atTop.mpr tendsto_id))

theorem survivingGreen_mean_tendsto_zero (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) :
    Tendsto (fun T : ℝ≥0 => ∫ b, survivingGreen a T b z.1 ∂W) atTop (𝓝 0) := by
  simpa only [survivingGreen_eq_killed,integral_const_mul,mul_zero] using
    (killedGreen_mean_tendsto_zero a ha W hW z).const_mul (Real.exp (-alpha a*Real.log 2))

theorem survivingGreen_lintegral_tendsto_zero (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) :
    Tendsto (fun T : ℝ≥0 => ∫⁻ b, ENNReal.ofReal (survivingGreen a T b z.1) ∂W)
      atTop (𝓝 0) := by
  have he (T : ℝ≥0) : ENNReal.ofReal (∫ b, survivingGreen a T b z.1 ∂W) =
      ∫⁻ b, ENNReal.ofReal (survivingGreen a T b z.1) ∂W :=
    ofReal_integral_eq_lintegral_ofReal ((actual_surviving_green a ha T).2.2 W hW z.1 z.2).1
      (Eventually.of_forall (fun b => by
        change 0 ≤ survivingGreen a T b z.1
        rw [survivingGreen_eq_killed]
        exact mul_nonneg (Real.exp_pos _).le (killedGreen_nonneg a z T b)))
  simpa only [he,ENNReal.ofReal_zero] using
    ENNReal.tendsto_ofReal (survivingGreen_mean_tendsto_zero a ha W hW z)

end ExactSLEGreen
end
 

 
section
 

open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma survivingGreen_lintegral_le_initial (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (z : UpperPlane) :
    (∫⁻b, ENNReal.ofReal (survivingGreen a t b z.1) ∂W) ≤
      ENNReal.ofReal (initialGreen a z) := by
  obtain ⟨hi,hb⟩ := (actual_surviving_green a ha t).2.2 W hW z.1 z.2
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun b => survivingGreen_nonneg a t b z.1))]
  exact ENNReal.ofReal_le_ofReal hb

 

theorem survivingGreen_compact_mean_tendsto_zero (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (K : Set UpperPlane) (hK : IsCompact K) :
    Tendsto (fun n : ℕ => ∫⁻b, ∫⁻z in K,
      ENNReal.ofReal (survivingGreen a n b z.1) ∂upperArea ∂W) atTop (𝓝 0) := by
  have hm (n : ℕ) : Measurable (fun z : UpperPlane =>
      ∫⁻b, ENNReal.ofReal (survivingGreen a n b z.1) ∂W) :=
    (survivingGreen_joint_measurable a ha n).ennreal_ofReal.lintegral_prod_left
  have hb (n : ℕ) : (fun z : UpperPlane =>
        ∫⁻b, ENNReal.ofReal (survivingGreen a n b z.1) ∂W) ≤ᵐ[upperArea.restrict K]
      (fun z => ENNReal.ofReal (initialGreen a z)) :=
    Eventually.of_forall (survivingGreen_lintegral_le_initial a ha W hW n)
  have hf : (∫⁻z in K, ENNReal.ofReal (initialGreen a z) ∂upperArea) ≠ ∞ := by
    rw [← withDensity_apply _ hK.measurableSet]
    change initialGreenMeasure a K ≠ ∞
    exact hK.measure_lt_top.ne
  have hlim : ∀ᵐ z ∂upperArea.restrict K,
      Tendsto (fun n : ℕ => ∫⁻b, ENNReal.ofReal (survivingGreen a n b z.1) ∂W)
        atTop (𝓝 (0 : ℝ≥0∞)) := Eventually.of_forall (fun z =>
    (survivingGreen_lintegral_tendsto_zero a ha W hW z).comp tendsto_natCast_atTop_atTop)
  have h := tendsto_lintegral_of_dominated_convergence
    (fun z => ENNReal.ofReal (initialGreen a z)) hm hb hf hlim
  simp only [lintegral_zero] at h
  convert h using 1
  funext n
  exact lintegral_lintegral_swap
    (survivingGreen_joint_measurable a ha n).ennreal_ofReal.aemeasurable

end ExactSLEGreen
end

end OAI
