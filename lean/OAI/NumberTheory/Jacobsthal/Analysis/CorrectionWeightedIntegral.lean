import OAI.NumberTheory.Jacobsthal.Estimates.CorrectionEnvelope

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.InvariantInverseWeights
open NumberTheoryLean.PrimeOccupationDensity NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.InvariantCostBound

noncomputable def densityEnvelope (c : ℝ) (x : ℝ×State) : ℝ :=
  density 2 x*Real.exp (-c*Real.exp x.1)

theorem densityEnvelope_nonneg (c : ℝ) (x : ℝ×State) : 0 ≤ densityEnvelope c x :=
  mul_nonneg (density_nonneg 2 x) (Real.exp_pos _).le

theorem densityEnvelope_measurable (c : ℝ) : Measurable (densityEnvelope c) :=
  (density_measurable 2).mul (Real.measurable_exp.comp
    (measurable_const.mul (Real.measurable_exp.comp measurable_fst)))

theorem densityEnvelope_factor (c u : ℝ) (s : State) :
    ENNReal.ofReal (densityEnvelope c (u,s))=
      ENNReal.ofReal ((Real.exp u)^2*Real.exp (-c*Real.exp u)/costMass)*
        inverseWeightCutoff (Real.exp u/2) s := by
  classical
  by_cases h : stateRatio s < Real.exp u/2
  · rw [inverseWeightCutoff,indicator_of_mem (show s ∈ {s | stateRatio s < Real.exp u/2} from h)]
    unfold densityEnvelope density
    rw [ite_eq_left h]
    have he : (Real.exp u)^2/(stateWeight s*costMass)*Real.exp (-c*Real.exp u)=
        ((Real.exp u)^2*Real.exp (-c*Real.exp u)/costMass)/stateWeight s := by ring
    rw [he,ENNReal.ofReal_div_of_pos (stateWeight_pos s),div_eq_mul_inv]
  · rw [inverseWeightCutoff,indicator_of_notMem (show s ∉ {s | stateRatio s < Real.exp u/2} from h),mul_zero]
    simp only [densityEnvelope,density,ite_eq_right h,zero_mul,ENNReal.ofReal_zero]

theorem densityEnvelope_section_le (c u : ℝ) :
    (∫⁻ s : State,ENNReal.ofReal (densityEnvelope c (u,s)) ∂stateMeasure) ≤
      ENNReal.ofReal ((Real.exp u)^3*Real.exp (-c*Real.exp u)/costMass) := by
  simp_rw [densityEnvelope_factor]
  rw [lintegral_const_mul _ (inverseWeightCutoff_measurable _)]
  have hb := inverseWeightCutoff_mass_le (L := Real.exp u/2) (by positivity)
  have hc : 0 ≤ (Real.exp u)^2*Real.exp (-c*Real.exp u)/costMass :=
    div_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) costMass_pos.le
  calc
    _ ≤ ENNReal.ofReal ((Real.exp u)^2*Real.exp (-c*Real.exp u)/costMass)*
        ENNReal.ofReal (2*(Real.exp u/2)) := mul_le_mul le_rfl hb (by positivity) (by positivity)
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; ring

theorem densityEnvelope_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (densityEnvelope c) baseMeasure := by
  have hgn : ∀ u : ℝ,0 ≤ (Real.exp u)^3*Real.exp (-c*Real.exp u)/costMass :=
    fun u => div_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (Real.exp_pos _).le) costMass_pos.le
  have hgi : Integrable (fun u : ℝ => (Real.exp u)^3*Real.exp (-c*Real.exp u)/costMass) := by
    simpa only [Nat.reduceAdd] using (exp_gap_moment_integrable 2 hc).div_const costMass
  refine ⟨(densityEnvelope_measurable c).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (densityEnvelope_nonneg c))).mpr
  have hm : Measurable (fun x => ENNReal.ofReal (densityEnvelope c x)) :=
    ENNReal.measurable_ofReal.comp (densityEnvelope_measurable c)
  rw [baseMeasure,lintegral_prod _ hm.aemeasurable]
  exact (lintegral_mono (densityEnvelope_section_le c)).trans_lt
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hgn)).mp hgi.hasFiniteIntegral)

theorem fullRaw_integrable : Integrable (rawTest fullAnomalyTest) (limitingMeasure 2) := by
  obtain ⟨C,c,hC,hc,ha⟩ := full_anomaly_exponential
  have hm := rawTest_measurable fullAnomalyTest_continuous
  have hD := ENNReal.measurable_ofReal.comp (density_measurable 2)
  have ht : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density 2 x)<∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  apply (integrable_withDensity_iff_integrable_smul' hD ht).mpr
  have hi : Integrable (fun x => density 2 x*rawTest fullAnomalyTest x) baseMeasure := by
    apply ((densityEnvelope_integrable hc).const_mul C).mono'
      ((density_measurable 2).mul hm).aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    change ‖density 2 x*rawTest fullAnomalyTest x‖ ≤ C*densityEnvelope c x
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (density_nonneg 2 x)]
    have hb := mul_le_mul_of_nonneg_left (ha (stateSide x.2) (Real.exp x.1)) (density_nonneg 2 x)
    change density 2 x*|extendedSignedAnomaly (stateSide x.2) (Real.exp x.1)| ≤ _
    unfold densityEnvelope
    nlinarith
  apply hi.congr
  filter_upwards with x
  change density 2 x*rawTest fullAnomalyTest x = (ENNReal.ofReal (density 2 x)).toReal • rawTest fullAnomalyTest x
  rw [ENNReal.toReal_ofReal (density_nonneg 2 x),smul_eq_mul]

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PrimeOccupationDensity NumberTheoryLean.OccupationDensityIntegral
open NumberTheoryLean.CompactLogOccupationTest NumberTheoryLean.NormalizedOccupationLimit
open NumberTheoryLean.TransitionKernels NumberTheoryLean.OccupationBoundaries
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.OrdinaryKernelInvariance
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness

theorem invariant_ratio_ge_one : ∀ᵐ s : State ∂stateMeasure,1 ≤ stateRatio s := by
  have hp : MeasurableSet {s : State | 1 ≤ stateRatio s} :=
    measurableSet_le measurable_const stateRatio_measurable
  rw [stateMeasure,ae_add_measure_iff]
  constructor
  · apply (ae_map_iff measurable_inl.aemeasurable hp).mpr
    exact Eventually.of_forall (fun s => by change 1 ≤ s.1; linarith [s.2])
  · apply (ae_map_iff measurable_inr.aemeasurable hp).mpr
    rw [oddStateMeasure]
    apply (ae_map_iff oddLift_measurable.aemeasurable
      (measurableSet_le measurable_const measurable_subtype_coe)).mpr
    have hm : Measurable (fun t => ENNReal.ofReal (Erdos970Dependency.InvariantDensities.oddDensity t)) :=
      ENNReal.measurable_ofReal.comp Erdos970Dependency.InvariantDensities.oddDensity_measurable
    unfold oddMeasure
    apply (ae_withDensity_iff hm).mpr
    apply Eventually.of_forall
    intro t ht
    by_cases h : 1 ≤ t
    · change 1 ≤ max (95/100:ℝ) t
      exact h.trans (le_max_right _ _)
    · exfalso
      apply ht
      rw [Erdos970Dependency.InvariantDensities.oddDensity,indicator_of_notMem (show t ∉ Ici (1:ℝ) from h),ENNReal.ofReal_zero]

theorem limiting_gap_ge_two : ∀ᵐ x : ℝ×State ∂limitingMeasure 2,2 ≤ Real.exp x.1 := by
  have hbase : ∀ᵐ x : ℝ×State ∂baseMeasure,1 ≤ stateRatio x.2 := by
    have hset : MeasurableSet {x : ℝ×State | 1 ≤ stateRatio x.2} :=
      measurableSet_le measurable_const (stateRatio_measurable.comp measurable_snd)
    exact (Measure.ae_prod_iff_ae_ae hset).mpr (Eventually.of_forall (fun _ => invariant_ratio_ge_one))
  have hm : Measurable (fun x => ENNReal.ofReal (density 2 x)) :=
    ENNReal.measurable_ofReal.comp (density_measurable 2)
  rw [limitingMeasure,ae_withDensity_iff hm]
  filter_upwards [hbase] with x hx hd
  have harr : stateRatio x.2 < Real.exp x.1/2 := by
    by_contra h
    exact hd (by simp only [density,ite_eq_right h,ENNReal.ofReal_zero])
  linarith

theorem compact_raw_tendsto :
    ∀ᵐ x : ℝ×State ∂limitingMeasure 2,
      Tendsto (fun K : ℝ => rawTest (compactAnomalyTest K) x) atTop
        (𝓝 (rawTest fullAnomalyTest x)) := by
  filter_upwards [limiting_gap_ge_two] with x hx
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (max (Real.exp x.1) (stateRatio x.2))] with K hK
  have hrK : Real.exp x.1 ≤ K := (le_max_left _ _).trans hK
  have hsK : stateRatio x.2 ≤ K := (le_max_right _ _).trans hK
  change extendedSignedAnomaly (stateSide x.2) (Real.exp x.1)=
    compactCutoff K (Real.exp x.1,stateRatio x.2)*extendedSignedAnomaly (stateSide x.2) (Real.exp x.1)
  rw [(compactCutoff_spec K).2.2.1 _ _ hx hrK (stateRatio_pos _).le hsK,one_mul]

theorem compact_raw_norm_le (K : ℝ) (x : ℝ×State) :
    ‖rawTest (compactAnomalyTest K) x‖ ≤ ‖rawTest fullAnomalyTest x‖ := by
  have hb := (compactCutoff_spec K).2.1 (Real.exp x.1,stateRatio x.2)
  change ‖compactCutoff K (Real.exp x.1,stateRatio x.2)*extendedSignedAnomaly (stateSide x.2) (Real.exp x.1)‖ ≤
    ‖extendedSignedAnomaly (stateSide x.2) (Real.exp x.1)‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_nonneg hb.1]
  exact mul_le_of_le_one_left (abs_nonneg _) hb.2

theorem compact_limiting_integral_tendsto :
    Tendsto (fun K : ℝ => ∫ x,rawTest (compactAnomalyTest K) x ∂limitingMeasure 2) atTop
      (𝓝 (∫ x,rawTest fullAnomalyTest x ∂limitingMeasure 2)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖rawTest fullAnomalyTest x‖)
  · exact Eventually.of_forall (fun K => (rawTest_measurable (compactAnomalyTest_continuous K)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun K => Eventually.of_forall (compact_raw_norm_le K))
  · exact fullRaw_integrable.norm
  · exact compact_raw_tendsto

theorem compact_invariant_tendsto :
    Tendsto (fun K : ℝ => invariantAverage (arrivalTest 2 (compactAnomalyTest K))) atTop
      (𝓝 (∫ x,rawTest fullAnomalyTest x ∂limitingMeasure 2)) := by
  apply compact_limiting_integral_tendsto.congr'
  filter_upwards [eventually_ge_atTop (3:ℝ)] with K hK
  exact (continuous_test_density (compactAnomalyTest_continuous K) (compactAnomalyTest_compact K)
    (a := 1) (b := K+1) (by norm_num) (by linarith) (by norm_num : (0:ℝ)<2)
    (fun i r s hr => compactAnomalyTest_support K i r s hr)).2

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PrimeOccupationDensity
open NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.StateKernelInvariance

noncomputable def fullWeighted (x : ℝ×State) : ℝ := density 2 x*rawTest fullAnomalyTest x

theorem fullWeighted_measurable : Measurable fullWeighted :=
  (density_measurable 2).mul (rawTest_measurable fullAnomalyTest_continuous)

theorem fullWeighted_integrable : Integrable fullWeighted baseMeasure := by
  have hD : Measurable (fun x => ENNReal.ofReal (density 2 x)) :=
    ENNReal.measurable_ofReal.comp (density_measurable 2)
  have ht : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density 2 x)<∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hi := (integrable_withDensity_iff_integrable_smul' hD ht).mp fullRaw_integrable
  apply hi.congr
  filter_upwards with x
  change (ENNReal.ofReal (density 2 x)).toReal • rawTest fullAnomalyTest x=fullWeighted x
  rw [ENNReal.toReal_ofReal (density_nonneg 2 x),smul_eq_mul]
  rfl

theorem densityEnvelope_section_integrable (c u : ℝ) :
    Integrable (fun s : State => densityEnvelope c (u,s)) stateMeasure := by
  have hm : Measurable (fun s : State => densityEnvelope c (u,s)) := (densityEnvelope_measurable c).comp (measurable_const.prodMk measurable_id)
  refine ⟨hm.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun s => densityEnvelope_nonneg c (u,s)))).mpr
  exact (densityEnvelope_section_le c u).trans_lt ENNReal.ofReal_lt_top

theorem fullWeighted_section_integrable (u : ℝ) :
    Integrable (fun s : State => fullWeighted (u,s)) stateMeasure := by
  obtain ⟨C,c,hC,_hc,ha⟩ := full_anomaly_exponential
  have hm : Measurable (fun s : State => fullWeighted (u,s)) := fullWeighted_measurable.comp (measurable_const.prodMk measurable_id)
  apply ((densityEnvelope_section_integrable c u).const_mul C).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro s
  change ‖density 2 (u,s)*rawTest fullAnomalyTest (u,s)‖ ≤ C*densityEnvelope c (u,s)
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (density_nonneg 2 (u,s))]
  have hb := mul_le_mul_of_nonneg_left (ha (stateSide s) (Real.exp u)) (density_nonneg 2 (u,s))
  change density 2 (u,s)*|extendedSignedAnomaly (stateSide s) (Real.exp u)| ≤ _
  unfold densityEnvelope
  nlinarith

theorem full_limiting_integral_fubini :
    (∫ x,rawTest fullAnomalyTest x ∂limitingMeasure 2)=
      ∫ u : ℝ,∫ s : State,fullWeighted (u,s) ∂stateMeasure := by
  have hD : Measurable (fun x => ENNReal.ofReal (density 2 x)) :=
    ENNReal.measurable_ofReal.comp (density_measurable 2)
  have ht : ∀ᵐ x ∂baseMeasure,ENNReal.ofReal (density 2 x)<∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [limitingMeasure,integral_withDensity_eq_integral_toReal_smul hD ht]
  have he : (fun x => (ENNReal.ofReal (density 2 x)).toReal • rawTest fullAnomalyTest x)=fullWeighted := by
    funext x
    rw [ENNReal.toReal_ofReal (density_nonneg 2 x),smul_eq_mul]
    rfl
  rw [he]
  exact integral_prod fullWeighted fullWeighted_integrable

end ErdosCorrectionLimit

end

end Erdos970

end OAI
