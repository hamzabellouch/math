import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.BrownianShifts

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.StoppingRounding

def round (n : ℕ) (t : ℝ≥0) : ℝ≥0 := (⌈((n+1:ℕ):ℝ≥0)*t⌉₊ : ℝ≥0)/(n+1:ℕ)

theorem le_round (n : ℕ) (t : ℝ≥0) : t≤round n t := by
  have hd : (0:ℝ≥0)<(n+1:ℕ) := by positivity
  rw [round,le_div_iff₀ hd]
  simpa only [mul_comm] using Nat.le_ceil (((n+1:ℕ):ℝ≥0)*t)

theorem round_le (n : ℕ) (t : ℝ≥0) : round n t≤t+((n+1:ℕ):ℝ≥0)⁻¹ := by
  have hd : (0:ℝ≥0)<(n+1:ℕ) := by positivity
  rw [round,div_le_iff₀ hd,add_mul,inv_mul_cancel₀ hd.ne']
  exact (Nat.ceil_lt_add_one (bot_le (a:=((n+1:ℕ):ℝ≥0)*t))).le.trans_eq (by rw [mul_comm])

theorem round_le_iff (n : ℕ) (s t : ℝ≥0) :
    round n s≤t ↔ s≤(⌊((n+1:ℕ):ℝ≥0)*t⌋₊ : ℝ≥0)/(n+1:ℕ) := by
  have hd : (0:ℝ≥0)<(n+1:ℕ) := by positivity
  rw [round,div_le_iff₀ hd,←Nat.le_floor_iff (bot_le (a:=t*((n+1:ℕ):ℝ≥0))),
    Nat.ceil_le,le_div_iff₀ hd]
  simp only [mul_comm]

theorem floor_time_le (n : ℕ) (t : ℝ≥0) :
    (⌊((n+1:ℕ):ℝ≥0)*t⌋₊ : ℝ≥0)/(n+1:ℕ)≤t := by
  have hd : (0:ℝ≥0)<(n+1:ℕ) := by positivity
  rw [div_le_iff₀ hd]
  simpa only [mul_comm] using Nat.floor_le (bot_le (a:=((n+1:ℕ):ℝ≥0)*t))

theorem countable_range (n : ℕ) : (Set.range (round n)).Countable := by
  apply (Set.countable_range (fun k : ℕ => (k:ℝ≥0)/(n+1:ℕ))).mono
  rintro _ ⟨t,rfl⟩
  exact ⟨_,rfl⟩

theorem tendsto_round (t : ℝ≥0) : Tendsto (fun n => round n t) atTop (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
    (fun n => le_round n t) (fun n => round_le n t)
  have ht : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ≥0)⁻¹) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ≥0) |>.comp
      (tendsto_add_atTop_nat 1))
    exact h
  simpa only [add_zero] using tendsto_const_nhds.add ht

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ≥0 mΩ}
    {S : Ω→ℝ≥0}

theorem isStoppingTime (hS : IsStoppingTime ℱ (fun ω => (S ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (round n (S ω) : WithTop ℝ≥0)) := by
  intro t
  have h := hS ((⌊((n+1:ℕ):ℝ≥0)*t⌋₊ : ℝ≥0)/(n+1:ℕ))
  have he : {ω | (round n (S ω) : WithTop ℝ≥0)≤t} =
      {ω | (S ω : WithTop ℝ≥0)≤((⌊((n+1:ℕ):ℝ≥0)*t⌋₊ : ℝ≥0)/(n+1:ℕ) : ℝ≥0)} := by
    ext ω
    exact (WithTop.coe_le_coe.trans (round_le_iff n (S ω) t)).trans WithTop.coe_le_coe.symm
  rw [he]
  exact ℱ.mono (floor_time_le n t) _ h

end SLEExactGauge.StoppingRounding
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped NNReal ENNReal ContinuousMapZero BoundedContinuousFunction
namespace SLEExactGauge.BrownianRestart

def filtration : Filtration ℝ≥0 instMeasurableSpaceDriver :=
  Filtration.natural (fun t (b : Driver) => b t)
    (fun t => (continuous_eval_const t).stronglyMeasurable)

lemma continuous_shift_joint : Continuous (fun p : ℝ≥0×Driver => shift p.1 p.2) := by
  apply ContinuousMapZero.isEmbedding_toContinuousMap.continuous_iff.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (ℝ≥0×Driver)×ℝ≥0 => p.1.2 (p.1.1+p.2)-p.1.2 p.1.1)
  exact (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
    ((continuous_fst.comp continuous_fst).add continuous_snd))).sub
    (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
      (continuous_fst.comp continuous_fst)))

lemma indep_filtration_shift {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W) (t : ℝ≥0) :
    Indep (filtration t) (MeasurableSpace.comap (shift t) inferInstance) W := by
  rw [filtration, Filtration.natural_eq_comap]
  change IndepFun (fun b : Driver => fun s : Iic t => b s) (shift t) W
  exact (indep_shift_history hW t).symm

lemma integral_shift {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W) (t : ℝ≥0) (f : Driver →ᵇ ℝ) :
    (∫b,f (shift t b)∂W)=∫b,f b∂W := by
  rw [← integral_map (measurable_shift t).aemeasurable f.continuous.aestronglyMeasurable,
    shift_preserves_law hW t]

lemma setIntegral_shift {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W) (t : ℝ≥0)
    {A : Set Driver} (hA : MeasurableSet[filtration t] A) (f : Driver →ᵇ ℝ) :
    (∫b in A,f (shift t b)∂W)=∫_b in A,(∫b,f b∂W)∂W := by
  rw [(indep_filtration_shift hW t).setIntegral_eq_mul (filtration.le t)
    (measurable_shift t).aemeasurable hA f.continuous.aestronglyMeasurable,
    integral_shift hW t f]
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]

lemma measurable_finite_stop {T : Driver→ℝ≥0}
    (hT : IsStoppingTime filtration (fun b => (T b : WithTop ℝ≥0))) : Measurable T := by
  apply measurable_of_Iic
  intro t
  convert filtration.le t _ (hT t) using 1
  ext b
  change T b ≤ t ↔ (T b : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)
  exact WithTop.coe_le_coe.symm

lemma measurable_shift_finite_stop {T : Driver→ℝ≥0}
    (hT : IsStoppingTime filtration (fun b => (T b : WithTop ℝ≥0))) :
    Measurable (fun b => shift (T b) b) :=
  continuous_shift_joint.measurable.comp ((measurable_finite_stop hT).prodMk measurable_id)

lemma integrable_bcf_comp {W : Measure Driver} [IsFiniteMeasure W]
    (f : Driver →ᵇ ℝ) {Y : Driver→Driver} (hY : Measurable Y) :
    Integrable (fun b => f (Y b)) W := by
  apply Integrable.mono' (integrable_const ‖f‖)
    (f.continuous.measurable.comp hY).aestronglyMeasurable
  exact Eventually.of_forall (fun b => f.norm_coe_le_norm (Y b))

 
theorem setIntegral_shift_countable {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {T : Driver→ℝ≥0} (hT : IsStoppingTime filtration (fun b => (T b : WithTop ℝ≥0)))
    (hc : (Set.range T).Countable) {A : Set Driver}
    (hA : MeasurableSet[hT.measurableSpace] A) (f : Driver →ᵇ ℝ) :
    (∫b in A,f (shift (T b) b)∂W)=∫_b in A,(∫b,f b∂W)∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let : Countable (Set.range T) := hc.to_subtype
  let U : Set.range T→Set Driver := fun t => A∩{b | T b=t.1}
  have hm (t : Set.range T) : MeasurableSet[filtration t.1] (U t) := by
    have h := hA.inter (hT.measurableSet_eq' t.1)
    have h' := (hT.measurableSet_inter_eq_iff A t.1).mp h
    simpa only [U,WithTop.coe_eq_coe] using h'
  have hm' (t : Set.range T) : MeasurableSet (U t) := filtration.le t.1 _ (hm t)
  have hd : Pairwise (Disjoint on U) := by
    intro t u htu
    apply disjoint_left.mpr
    intro b hb hc
    exact htu (Subtype.ext (hb.2.symm.trans hc.2))
  have hU : (⋃t,U t)=A := by
    ext b
    simp only [mem_iUnion,U,mem_inter_iff,mem_ofPred_eq]
    constructor
    · rintro ⟨t,h,_⟩; exact h
    · intro hb; exact ⟨⟨T b,mem_range_self b⟩,hb,rfl⟩
  have hi := integrable_bcf_comp f (measurable_shift_finite_stop hT) (W:=W)
  calc
    (∫b in A,f (shift (T b) b)∂W) = ∑'t,∫b in U t,f (shift (T b) b)∂W := by
      rw [←hU, integral_iUnion hm' hd hi.integrableOn]
    _ = ∑'t,∫_b in U t,(∫b,f b∂W)∂W := by
      apply tsum_congr
      intro t
      rw [setIntegral_congr_fun (hm' t) (fun b hb => by rw [hb.2])]
      exact setIntegral_shift hW t.1 (hm t) f
    _ = ∫_b in A,(∫b,f b∂W)∂W := by
      rw [←hU,integral_iUnion hm' hd (integrable_const _).integrableOn]

 

theorem setIntegral_shift_finite {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {T : Driver→ℝ≥0} (hT : IsStoppingTime filtration (fun b => (T b : WithTop ℝ≥0)))
    {A : Set Driver} (hA : MeasurableSet[hT.measurableSpace] A) (f : Driver →ᵇ ℝ) :
    (∫b in A,f (shift (T b) b)∂W)=∫_b in A,(∫b,f b∂W)∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let Tn := fun n b => StoppingRounding.round n (T b)
  have hn (n : ℕ) : IsStoppingTime filtration (fun b => (Tn n b : WithTop ℝ≥0)) :=
    StoppingRounding.isStoppingTime hT n
  have hAn (n : ℕ) : MeasurableSet[(hn n).measurableSpace] A :=
    (hT.measurableSpace_mono (hn n) (fun b => WithTop.coe_le_coe.mpr
      (StoppingRounding.le_round n (T b)))) _ hA
  have he (n : ℕ) : (∫b in A,f (shift (Tn n b) b)∂W)=∫_b in A,(∫b,f b∂W)∂W := by
    apply setIntegral_shift_countable hW (hn n) _ (hAn n) f
    exact (StoppingRounding.countable_range n).mono (Set.range_comp_subset_range T (StoppingRounding.round n))
  have ht : Tendsto (fun n => ∫b in A,f (shift (Tn n b) b)∂W) atTop
      (𝓝 (∫b in A,f (shift (T b) b)∂W)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (f.continuous.measurable.comp (measurable_shift_finite_stop (hn n))).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall (fun b => f.norm_coe_le_norm _))
    apply Eventually.of_forall
    intro b
    exact f.continuous.continuousAt.tendsto.comp
      (continuous_shift_joint.continuousAt.tendsto.comp
        ((StoppingRounding.tendsto_round (T b)).prodMk_nhds tendsto_const_nhds))
  simp only [he] at ht
  exact (tendsto_nhds_unique tendsto_const_nhds ht).symm

 
theorem map_shift_finite {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {T : Driver→ℝ≥0} (hT : IsStoppingTime filtration (fun b => (T b : WithTop ℝ≥0))) :
    W.map (fun b => shift (T b) b)=W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (measurable_shift_finite_stop hT).aemeasurable
    f.continuous.aestronglyMeasurable]
  simpa using setIntegral_shift_finite hW hT MeasurableSet.univ f

 
theorem indep_shift_finite {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {T : Driver→ℝ≥0} (hT : IsStoppingTime filtration (fun b => (T b : WithTop ℝ≥0))) :
    Indep hT.measurableSpace (MeasurableSpace.comap (fun b => shift (T b) b) inferInstance) W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  apply indep_comap_of_bcf hT.measurableSpace_le (measurable_shift_finite_stop hT).aemeasurable
  intro A hA f
  rw [setIntegral_shift_finite hW hT hA f]
  rw [←integral_map (measurable_shift_finite_stop hT).aemeasurable
    f.continuous.aestronglyMeasurable,map_shift_finite hW hT]
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul]

end SLEExactGauge.BrownianRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped NNReal ENNReal ContinuousMapZero BoundedContinuousFunction
namespace SLEExactGauge.BrownianRestart

 

def shiftAt (S : Driver → ℝ≥0∞) (b : Driver) := shift (S b).toNNReal b

def truncateStop (S : Driver → ℝ≥0∞) (t : ℝ≥0) (b : Driver) : ℝ≥0 :=
  (min (S b) (t : ℝ≥0∞)).toNNReal

lemma coe_truncateStop (S : Driver → ℝ≥0∞) (t : ℝ≥0) :
    (fun b => (truncateStop S t b : WithTop ℝ≥0)) = fun b => min (S b) (t : WithTop ℝ≥0) := by
  funext b
  simp only [truncateStop, ENNReal.some_eq_coe']
  exact ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))

lemma isStoppingTime_truncateStop {S : Driver → ℝ≥0∞}
    (hS : IsStoppingTime filtration S) (t : ℝ≥0) :
    IsStoppingTime filtration (fun b => (truncateStop S t b : WithTop ℝ≥0)) := by
  rw [coe_truncateStop]
  exact hS.min_const t

lemma measurable_shiftAt {S : Driver → ℝ≥0∞} (hS : IsStoppingTime filtration S) :
    Measurable (shiftAt S) := by
  exact continuous_shift_joint.measurable.comp
    ((ENNReal.measurable_toNNReal.comp hS.measurable').prodMk measurable_id)

lemma finiteStop_iUnion_le (S : Driver → ℝ≥0∞) :
    (⋃ n : ℕ, {b | S b ≤ (n : ℝ≥0∞)}) = {b | S b ≠ ∞} := by
  ext b
  simp only [mem_iUnion, mem_ofPred_eq]
  constructor
  · rintro ⟨n,hn⟩
    exact ne_top_of_le_ne_top (by simp) hn
  · intro hb
    exact (ENNReal.exists_nat_gt hb).imp (fun _ h => h.le)

lemma setIntegral_shiftAt_le {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {S : Driver → ℝ≥0∞} (hS : IsStoppingTime filtration S)
    {A : Set Driver} (hA : MeasurableSet[hS.measurableSpace] A)
    (t : ℝ≥0) (f : Driver →ᵇ ℝ) :
    (∫b in A ∩ {b | S b ≤ (t : ℝ≥0∞)}, f (shiftAt S b) ∂W) =
      ∫_b in A ∩ {b | S b ≤ (t : ℝ≥0∞)}, (∫b, f b ∂W) ∂W := by
  have he := coe_truncateStop S t
  have hA' : MeasurableSet[(isStoppingTime_truncateStop hS t).measurableSpace]
      (A ∩ {b | S b ≤ (t : ℝ≥0∞)}) := by
    have hspace : (isStoppingTime_truncateStop hS t).measurableSpace =
        (hS.min_const t).measurableSpace := by
      congr 1
    rw [hspace]
    convert (hS.measurableSet_inter_le_const_iff A t).mp
      (hA.inter (hS.measurableSet_le' t)) using 1
    simp only [ENNReal.some_eq_coe']
    rfl
  have h := setIntegral_shift_finite hW (isStoppingTime_truncateStop hS t) hA' f
  rw [←h]
  apply setIntegral_congr_fun
  · exact hS.measurableSpace_le _ (hA.inter (measurableSet_le (show Measurable[hS.measurableSpace] S from hS.measurable) measurable_const))
  · intro b hb
    simp only [shiftAt, truncateStop, min_eq_left (show S b ≤ (t : ℝ≥0∞) from hb.2)]

 

theorem setIntegral_shiftAt_finite {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {S : Driver → ℝ≥0∞} (hS : IsStoppingTime filtration S)
    {A : Set Driver} (hA : MeasurableSet[hS.measurableSpace] A) (f : Driver →ᵇ ℝ) :
    (∫b in A ∩ {b | S b ≠ ∞}, f (shiftAt S b) ∂W) =
      ∫_b in A ∩ {b | S b ≠ ∞}, (∫b, f b ∂W) ∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let U : ℕ → Set Driver := fun n => A ∩ {b | S b ≤ (n : ℝ≥0∞)}
  have hmeas n : MeasurableSet (U n) :=
    (hS.measurableSpace_le _ hA).inter (measurableSet_le (show Measurable S from hS.measurable') measurable_const)
  have hmono : Monotone U := by
    intro n m hnm b hb
    exact ⟨hb.1, (show S b ≤ (n : ℝ≥0∞) from hb.2).trans (Nat.cast_le.mpr hnm)⟩
  have hU : (⋃ n, U n) = A ∩ {b | S b ≠ ∞} := by
    simp only [U, ←inter_iUnion, finiteStop_iUnion_le]
  have h₁ := tendsto_setIntegral_of_monotone hmeas hmono
    (integrable_bcf_comp f (measurable_shiftAt hS) (W:=W)).integrableOn
  have h₂ := tendsto_setIntegral_of_monotone hmeas hmono
    (integrable_const (∫b, f b ∂W) (μ:=W)).integrableOn
  have he (n : ℕ) : (∫b in U n, f (shiftAt S b) ∂W) =
      ∫_b in U n, (∫b, f b ∂W) ∂W := by
    simpa only [U, ENNReal.coe_natCast] using setIntegral_shiftAt_le hW hS hA (n:ℝ≥0) f
  simp only [hU, he] at h₁ h₂
  exact tendsto_nhds_unique h₁ h₂

 

theorem map_shiftAt_restrict {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {S : Driver → ℝ≥0∞} (hS : IsStoppingTime filtration S)
    {A : Set Driver} (hA : MeasurableSet[hS.measurableSpace] A) :
    (W.restrict (A ∩ {b | S b ≠ ∞})).map (shiftAt S) =
      W (A ∩ {b | S b ≠ ∞}) • W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (W (A ∩ {b | S b ≠ ∞}) • W) :=
    W.smul_finite (measure_ne_top W _)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (measurable_shiftAt hS).aemeasurable f.continuous.aestronglyMeasurable,
    setIntegral_shiftAt_finite hW hS hA f, integral_smul_measure]
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ]

 

theorem map_data_shiftAt {X : Type*} [MeasurableSpace X] {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {S : Driver → ℝ≥0∞} (hS : IsStoppingTime filtration S)
    {D : Driver → X} (hD : Measurable[hS.measurableSpace] D) :
    (W.restrict {b | S b ≠ ∞}).map (fun b => (D b,shiftAt S b)) =
      ((W.restrict {b | S b ≠ ∞}).map D).prod W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hD' : Measurable D := hD.mono hS.measurableSpace_le le_rfl
  have hY := measurable_shiftAt hS
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply (hD'.prodMk hY) (hA.prod hB), Measure.prod_prod,
    Measure.map_apply hD' hA, Measure.restrict_apply (hD' hA)]
  have he := congrArg (fun μ : Measure Driver => μ B)
    (map_shiftAt_restrict hW hS (hD hA))
  rw [Measure.map_apply hY hB, Measure.restrict_apply (hY hB), Measure.smul_apply,
    smul_eq_mul] at he
  rw [Measure.restrict_apply ((hD'.prodMk hY) (hA.prod hB))]
  convert he using 1
  congr 1
  ext b
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_ofPred_eq]
  tauto

 

theorem lintegral_data_shiftAt {X : Type*} [MeasurableSpace X] {W : Measure Driver}
    (hW : IsBrownianReal (fun t (b : Driver) => b t) W)
    {S : Driver → ℝ≥0∞} (hS : IsStoppingTime filtration S)
    {D : Driver → X} (hD : Measurable[hS.measurableSpace] D)
    {F : X × Driver → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻b in {b | S b ≠ ∞}, F (D b,shiftAt S b) ∂W) =
      ∫⁻b in {b | S b ≠ ∞}, ∫⁻c, F (D b,c) ∂W ∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hD' : Measurable D := hD.mono hS.measurableSpace_le le_rfl
  rw [←lintegral_map hF (hD'.prodMk (measurable_shiftAt hS)),map_data_shiftAt hW hS hD,
    lintegral_prod _ hF.aemeasurable, lintegral_map hF.lintegral_prod_right' hD']

end SLEExactGauge.BrownianRestart
end
end

end OAI
