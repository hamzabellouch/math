import Mathlib.Probability.Kernel.WithDensity
import OAI.NumberTheory.Jacobsthal.Partitions.BeginningWindowTransport

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.InitialRegeneration NumberTheoryLean.TransitionKernels
open NumberTheoryLean.KernelPotential
open AbsorptionCutoff.Renewal

noncomputable def rawFirstMarkedBeginning : Kernel OddCost OddCost :=
  (potential Kernel.id (cycleBranchKernel false)).withDensity (fun _ y => nextMarkWeight y)

lemma nextMarkWeight_ne_top (z : OddCost) : nextMarkWeight z ≠ ∞ :=
  measure_ne_top (cycleBranchKernel true z) univ

instance rawFirstMarkedBeginning_isSFiniteKernel : IsSFiniteKernel rawFirstMarkedBeginning := by
  unfold rawFirstMarkedBeginning
  exact Kernel.IsSFiniteKernel.withDensity _ (fun _ y => nextMarkWeight_ne_top y)

lemma rawFirstMarkedBeginning_apply (z : OddCost) :
    rawFirstMarkedBeginning z =
      Measure.sum (fun n : ℕ => ((cycleBranchKernel false ^ n) z).withDensity nextMarkWeight) := by
  rw [rawFirstMarkedBeginning,Kernel.withDensity_apply _ (f := fun _ y : OddCost => nextMarkWeight y) (nextMarkWeight_measurable.comp measurable_snd),
    potential,Kernel.sum_apply]
  simp only [Kernel.id_comp]
  exact withDensity_sum _ _

lemma rawFirstMarkedBeginning_increment (z : OddCost) (hz : z ∈ returnSet) :
    (rawFirstMarkedBeginning z).map (fun y => y.2-z.2) = firstMarkWaitingLaw := by
  rw [rawFirstMarkedBeginning_apply,
    Measure.map_sum (f := fun y : OddCost => y.2-z.2) (measurable_snd.sub measurable_const).aemeasurable]
  change actualWaitingLaw z = firstMarkWaitingLaw
  rw [actualWaitingLaw_eq z hz,firstMarkWaitingLaw,actualWaitingLaw_eq]
  norm_num [returnSet,NumberTheoryLean.PairedHitting.pairedRegeneration,NumberTheoryLean.RegenerationTails.regenerationState]

lemma rawFirstMarkedBeginning_mass (z : OddCost) (hz : z ∈ returnSet) :
    rawFirstMarkedBeginning z univ = 1 := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) (rawFirstMarkedBeginning_increment z hz)
  rw [Measure.map_apply (f := fun y : OddCost => y.2-z.2) (measurable_snd.sub measurable_const) MeasurableSet.univ,preimage_univ] at he
  exact he.trans measure_univ

lemma rawFirstMarkedBeginning_ae_regeneration (z : OddCost) (hz : z ∈ returnSet) :
    ∀ᵐ y ∂rawFirstMarkedBeginning z, y ∈ returnSet := by
  rw [rawFirstMarkedBeginning_apply,Measure.ae_sum_iff]
  intro n
  exact (withDensity_absolutelyContinuous _ _).ae_le (cycleBranch_pow_ae_regeneration false n z hz)

lemma rawFirstMarkedBeginning_cost_integral (z : OddCost) (hz : z ∈ returnSet)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y.2 ∂rawFirstMarkedBeginning z) = ∫⁻ G, F (z.2+G) ∂firstMarkWaitingLaw := by
  rw [← rawFirstMarkedBeginning_increment z hz,
    lintegral_map (g := fun y : OddCost => y.2-z.2) (f := fun G : ℝ => F (z.2+G))
      (hF.comp (measurable_const.add measurable_id)) (measurable_snd.sub measurable_const)]
  apply lintegral_congr
  intro y
  congr 1
  ring

noncomputable def initialMarkedBeginning : Kernel EvenState OddCost :=
  rawFirstMarkedBeginning ∘ₖ delayedRegeneration

instance initialMarkedBeginning_isMarkovKernel : IsMarkovKernel initialMarkedBeginning := by
  constructor
  intro s
  constructor
  rw [initialMarkedBeginning,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  have he : (fun z => rawFirstMarkedBeginning z univ) =ᵐ[delayedRegeneration s] fun _ => 1 := by
    filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
    exact rawFirstMarkedBeginning_mass z hz
  rw [lintegral_congr_ae he]
  simp

lemma initialMarkedBeginning_ae_regeneration (s : EvenState) :
    ∀ᵐ z ∂initialMarkedBeginning s, z ∈ returnSet := by
  rw [initialMarkedBeginning]
  apply Kernel.ae_comp_of_ae_ae returnSet_measurable
  filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
  exact rawFirstMarkedBeginning_ae_regeneration z hz

noncomputable def initialMarkedCostLaw (s : EvenState) : Measure ℝ :=
  (initialMarkedBeginning s).map Prod.snd

instance initialMarkedCostLaw_isProbabilityMeasure (s : EvenState) : IsProbabilityMeasure (initialMarkedCostLaw s) :=
  (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance

lemma initialMarkedCostLaw_eq (s : EvenState) :
    initialMarkedCostLaw s = delayedCostLaw s ∗ firstMarkWaitingLaw := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [initialMarkedCostLaw,lintegral_map hF measurable_snd,initialMarkedBeginning,
    Kernel.lintegral_comp _ _ _ (g := fun z : OddCost => F z.2) (hF.comp measurable_snd),
    Measure.lintegral_conv hF,delayedCostLaw,
    lintegral_map (g := Prod.snd) (f := fun x : ℝ => ∫⁻ y, F (x+y) ∂firstMarkWaitingLaw)
      ((hF.comp measurable_add).lintegral_prod_right') measurable_snd]
  apply lintegral_congr_ae
  filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
  exact rawFirstMarkedBeginning_cost_integral z hz hF

lemma firstMarkWaiting_nonneg : ∀ᵐ G ∂firstMarkWaitingLaw, 0 ≤ G := by
  rw [firstMarkWaitingLaw,actualWaitingLaw_eq _ (by norm_num [returnSet,
    NumberTheoryLean.PairedHitting.pairedRegeneration,NumberTheoryLean.RegenerationTails.regenerationState])]
  exact Measure.ae_smul_measure unmarkedPotential_ae_nonneg _

lemma initialMarkedCost_nonneg (s : EvenState) : ∀ᵐ D ∂initialMarkedCostLaw s, 0 ≤ D := by
  rw [initialMarkedCostLaw_eq]
  have hd : ∀ᵐ T ∂delayedCostLaw s, 0 ≤ T := by
    rw [delayedCostLaw]
    exact (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr (delayedRegeneration_cost_nonneg s)
  simpa only [zero_add] using conv_ae_lower hd firstMarkWaiting_nonneg

lemma costTransform_mono {μ : Measure ℝ} (hμ : ∀ᵐ G ∂μ, 0 ≤ G) {a b : ℝ} (hab : a ≤ b) :
    costTransform μ a ≤ costTransform μ b := by
  apply lintegral_mono_ae
  filter_upwards [hμ] with G hG
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab hG))

theorem initialMarkedCost_uniform_exponential (S : ℝ) : ∃ eta B : ℝ, 0 < eta ∧ 0 ≤ B ∧
    ∀ s : EvenState, s.1 ≤ S → costTransform (initialMarkedCostLaw s) eta ≤ ENNReal.ofReal B := by
  obtain ⟨a,A,ha,hA,hDelay⟩ := delayedCostLaw_uniform_exponential S
  obtain ⟨b,hb,hWait,_⟩ := marked_waiting_common_exponential_moment
  let eta := min a b
  have heta : 0 < eta := lt_min ha hb
  have hW : costTransform firstMarkWaitingLaw eta < ∞ :=
    (costTransform_mono firstMarkWaiting_nonneg (min_le_right a b)).trans_lt hWait
  let W : ℝ := (costTransform firstMarkWaitingLaw eta).toReal
  have hWreal : costTransform firstMarkWaitingLaw eta = ENNReal.ofReal W :=
    (ENNReal.ofReal_toReal hW.ne).symm
  refine ⟨eta,A*W,heta,mul_nonneg hA ENNReal.toReal_nonneg,?_⟩
  intro s hs
  have hd : ∀ᵐ T ∂delayedCostLaw s, 0 ≤ T := by
    rw [delayedCostLaw]
    exact (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr (delayedRegeneration_cost_nonneg s)
  rw [initialMarkedCostLaw_eq,costTransform_conv,hWreal,ENNReal.ofReal_mul hA]
  exact mul_le_mul_left ((costTransform_mono hd (min_le_left a b)).trans (hDelay s hs)) _

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw
open NumberTheoryLean.TransitionKernels NumberTheoryLean.KernelPotential

noncomputable def initialBeginningReg : Kernel EvenState RegCost :=
  initialMarkedBeginning.comapRight (MeasurableEmbedding.subtype_coe returnSet_measurable)

instance initialBeginningReg_isMarkovKernel : IsMarkovKernel initialBeginningReg := by
  apply Kernel.IsMarkovKernel.comapRight
  intro s
  have he := (ae_mem_iff_measure_eq (μ := initialMarkedBeginning s)
    returnSet_measurable.nullMeasurableSet).mp (initialMarkedBeginning_ae_regeneration s)
  rw [measure_univ] at he
  convert! he using 1
  congr 1
  ext y
  simp

lemma initialBeginningReg_map_state (s : EvenState) :
    (initialBeginningReg s).map (Subtype.val : RegCost → OddCost) = initialMarkedBeginning s := by
  calc
    _ = (initialMarkedBeginning s).restrict returnSet := by
      change (((initialMarkedBeginning s).comap (Subtype.val : RegCost → OddCost)).map Subtype.val) = _
      exact map_comap_subtype_coe (μ := initialMarkedBeginning s) returnSet_measurable
    _ = _ := Measure.restrict_eq_self_of_ae_mem (initialMarkedBeginning_ae_regeneration s)

lemma initialBeginningReg_cost_law (s : EvenState) :
    (initialBeginningReg s).map beginningCost = initialMarkedCostLaw s := by
  rw [initialMarkedCostLaw,← initialBeginningReg_map_state s,
    Measure.map_map measurable_snd measurable_subtype_coe]
  rfl

lemma beginningBelow_shift (t v : ℝ) : beginningBelow t (v-t) = beginningBelow 0 v := by
  unfold beginningBelow
  congr 1
  ext z
  simp only [mem_preimage,mem_Iio,relativeBeginningCost,sub_zero]
  constructor <;> intro h <;> linarith

lemma beginningOver_shift (t v H : ℝ) : beginningOver t (v-t) H = beginningOver 0 v H := by
  unfold beginningOver
  congr 1
  ext z
  simp only [mem_preimage,mem_Ioi,relativeBeginningCost,sub_zero]
  constructor <;> intro h <;> linarith

lemma beginningWindow_shift (t v H : ℝ) : beginningWindow t (v-t) H = beginningWindow 0 v H := by
  unfold beginningWindow
  congr 1
  ext z
  simp only [mem_preimage,mem_Icc,relativeBeginningCost,sub_zero]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

lemma absoluteBeginningOvershoot_eq (z : RegCost) (v H : ℝ) :
    (potential (beginningOver 0 v H) (beginningBelow 0 v)) z univ =
      beginningOvershoot z (v-beginningCost z) H := by
  rw [beginningOvershoot,beginningOver_shift,beginningBelow_shift]

lemma absoluteBeginningWindowHit_eq (z : RegCost) (v H : ℝ) :
    (potential (beginningWindow 0 v H) (beginningBelow 0 v)) z univ =
      beginningWindowHit z (v-beginningCost z) H := by
  rw [beginningWindowHit,beginningWindow_shift,beginningBelow_shift]

noncomputable def markedWindowSuccess (v H : ℝ) (z : RegCost) : ℝ≥0∞ :=
  if beginningCost z < v then (potential (beginningWindow 0 v H) (beginningBelow 0 v)) z univ
  else if beginningCost z ≤ v+H then 1 else 0

noncomputable def markedWindowFailure (v H : ℝ) (z : RegCost) : ℝ≥0∞ :=
  if beginningCost z < v then (potential (beginningOver 0 v H) (beginningBelow 0 v)) z univ
  else if beginningCost z ≤ v+H then 0 else 1

lemma markedWindowSuccess_measurable (v H : ℝ) : Measurable (markedWindowSuccess v H) := by
  unfold markedWindowSuccess
  exact Measurable.ite (measurableSet_lt beginningCost_measurable measurable_const)
    ((potential _ _).measurable_coe MeasurableSet.univ)
    (Measurable.ite (measurableSet_le beginningCost_measurable measurable_const) measurable_const measurable_const)

lemma markedWindowFailure_measurable (v H : ℝ) : Measurable (markedWindowFailure v H) := by
  unfold markedWindowFailure
  exact Measurable.ite (measurableSet_lt beginningCost_measurable measurable_const)
    ((potential _ _).measurable_coe MeasurableSet.univ)
    (Measurable.ite (measurableSet_le beginningCost_measurable measurable_const) measurable_const measurable_const)

lemma markedWindow_partition (z : RegCost) (v H : ℝ) (hH : 0 ≤ H) :
    markedWindowSuccess v H z+markedWindowFailure v H z = 1 := by
  unfold markedWindowSuccess markedWindowFailure
  by_cases hz : beginningCost z < v
  · rw [ite_eq_left hz,ite_eq_left hz,absoluteBeginningOvershoot_eq,absoluteBeginningWindowHit_eq]
    exact beginningWindow_partition z (by linarith) hH
  · rw [ite_eq_right hz,ite_eq_right hz]
    split_ifs <;> simp

noncomputable def initialMarkedWindowSuccess (s : EvenState) (v H : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, markedWindowSuccess v H z ∂initialBeginningReg s

noncomputable def initialMarkedWindowFailure (s : EvenState) (v H : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, markedWindowFailure v H z ∂initialBeginningReg s

lemma initialMarkedWindow_partition (s : EvenState) (v H : ℝ) (hH : 0 ≤ H) :
    initialMarkedWindowSuccess s v H+initialMarkedWindowFailure s v H = 1 := by
  rw [initialMarkedWindowSuccess,initialMarkedWindowFailure,
    ← lintegral_add_left (markedWindowSuccess_measurable v H)]
  simp only [markedWindow_partition _ v H hH,lintegral_const,measure_univ,mul_one]

lemma cost_tail_le_transform (μ : Measure ℝ) {eta : ℝ} (heta : 0 ≤ eta) (v : ℝ) :
    μ (Ici v) ≤ ENNReal.ofReal (Real.exp (-eta*v))*costTransform μ eta := by
  calc
    _ = ∫⁻ G, (Ici v).indicator (fun _ => (1:ℝ≥0∞)) G ∂μ := by
      rw [lintegral_indicator measurableSet_Ici]; simp
    _ ≤ ∫⁻ G, ENNReal.ofReal (Real.exp (-eta*v))*ENNReal.ofReal (Real.exp (eta*G)) ∂μ := by
      apply lintegral_mono
      intro G
      by_cases hG : G ∈ Ici v
      · rw [indicator_of_mem hG]
        change (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (-eta*v))*ENNReal.ofReal (Real.exp (eta*G))
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
        have he : (1:ℝ) ≤ Real.exp (-eta*v+eta*G) := Real.one_le_exp_iff.mpr (by change v≤G at hG; nlinarith)
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he
      · rw [indicator_of_notMem hG]; exact zero_le
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma initialMarkedWindowFailure_le (s : EvenState) (v H R : ℝ)
    (hTail : ∀ z : RegCost, ∀ u : ℝ, 0 < u → beginningOvershoot z u H ≤ ENNReal.ofReal R) :
    initialMarkedWindowFailure s v H ≤ ENNReal.ofReal R+initialMarkedCostLaw s (Ici v) := by
  have hp (z : RegCost) : markedWindowFailure v H z ≤ ENNReal.ofReal R+
      (beginningCost ⁻¹' Ici v).indicator (fun _ => (1:ℝ≥0∞)) z := by
    by_cases hz : beginningCost z < v
    · rw [markedWindowFailure,ite_eq_left hz,absoluteBeginningOvershoot_eq,
        indicator_of_notMem (show z ∉ beginningCost ⁻¹' Ici v from not_le_of_gt hz),add_zero]
      exact hTail z _ (by linarith)
    · rw [indicator_of_mem (show z ∈ beginningCost ⁻¹' Ici v from le_of_not_gt hz),
        markedWindowFailure,ite_eq_right hz]
      split_ifs
      · exact zero_le
      · exact le_add_left le_rfl
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal R+(beginningCost ⁻¹' Ici v).indicator (fun _ => (1:ℝ≥0∞)) z ∂initialBeginningReg s :=
      lintegral_mono hp
    _ = ENNReal.ofReal R+initialBeginningReg s (beginningCost ⁻¹' Ici v) := by
      rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,
        lintegral_indicator (beginningCost_measurable measurableSet_Ici)]
      simp
    _ = _ := by
      rw [← initialBeginningReg_cost_law s,Measure.map_apply beginningCost_measurable measurableSet_Ici]

theorem initialMarkedWindow_exponential (S : ℝ) : ∃ eta C eta0 B : ℝ,
    0 < eta ∧ 0 < C ∧ 0 < eta0 ∧ 0 ≤ B ∧ ∀ s : EvenState, s.1 ≤ S → ∀ v H : ℝ,
      0 ≤ H → initialMarkedWindowFailure s v H ≤
        ENNReal.ofReal (C*Real.exp (-eta*H)+B*Real.exp (-eta0*v)) := by
  obtain ⟨eta,C,heta,hC,hTail⟩ := beginningWindow_exponential
  obtain ⟨eta0,B,heta0,hB,hDelay⟩ := initialMarkedCost_uniform_exponential S
  refine ⟨eta,C,eta0,B,heta,hC,heta0,hB,?_⟩
  intro s hs v H hH
  calc
    _ ≤ ENNReal.ofReal (C*Real.exp (-eta*H))+initialMarkedCostLaw s (Ici v) :=
      initialMarkedWindowFailure_le s v H _ (fun z u hu => (hTail z u H hu hH).1)
    _ ≤ ENNReal.ofReal (C*Real.exp (-eta*H))+
      ENNReal.ofReal (Real.exp (-eta0*v))*costTransform (initialMarkedCostLaw s) eta0 :=
      add_le_add le_rfl (cost_tail_le_transform _ heta0.le v)
    _ ≤ ENNReal.ofReal (C*Real.exp (-eta*H))+ENNReal.ofReal (Real.exp (-eta0*v))*ENNReal.ofReal B :=
      add_le_add le_rfl (mul_le_mul_right (hDelay s hs) _)
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,mul_comm (Real.exp (-eta0*v)),
      ← ENNReal.ofReal_add (mul_nonneg hC.le (Real.exp_pos _).le) (mul_nonneg hB (Real.exp_pos _).le)]

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ProbabilityTheory ENNReal
open NumberTheoryLean.TransitionKernels

lemma exponential_decay_tendsto {eta : ℝ} (heta : 0 < eta) (C : ℝ) :
    Tendsto (fun H : ℝ => C*Real.exp (-eta*H)) atTop (𝓝 0) := by
  have he : Tendsto (fun H : ℝ => Real.exp (-eta*H)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop heta tendsto_id)
  simpa only [mul_zero] using he.const_mul C

theorem moving_marked_window_capture {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ s : EvenState,
        199/100 ≤ s.1 → s.1 ≤ 23/10 →
        initialMarkedWindowFailure s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) ≤
          ENNReal.ofReal eps ∧
        1-ENNReal.ofReal eps ≤
          initialMarkedWindowSuccess s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) := by
  obtain ⟨eta,C,eta0,B,heta,_hC,heta0,_hB,hBound⟩ := initialMarkedWindow_exponential (23/10)
  have hHalf : 0 < eps/2 := by positivity
  obtain ⟨H,hH,hSmall⟩ := ((eventually_gt_atTop (0:ℝ)).and
    ((tendsto_order.mp (exponential_decay_tendsto heta C)).2 (eps/2) hHalf)).exists
  obtain ⟨V,hV⟩ := eventually_atTop.mp
    ((tendsto_order.mp (exponential_decay_tendsto heta0 B)).2 (eps/2) hHalf)
  let rho : ℝ := 10*Real.exp H
  have hrho : 10 < rho := by
    have he := Real.one_lt_exp_iff.mpr hH
    dsimp [rho]
    linarith
  have hWidth : Real.log (rho/10) = H := by
    dsimp [rho]
    rw [mul_div_cancel_left₀ _ (by norm_num : (10:ℝ) ≠ 0),Real.log_exp]
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [moving_window_cost_threshold hK (by linarith : 0 < rho) V] with w hw
  refine ⟨hw.1,?_⟩
  intro r hr s _hs0 hs1
  have hFailure : initialMarkedWindowFailure s
      (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) ≤ ENNReal.ofReal eps := by
    rw [hWidth]
    apply (hBound s hs1 _ H hH.le).trans
    apply ENNReal.ofReal_le_ofReal
    have htail := hV _ (hw.2 r hr)
    linarith
  refine ⟨hFailure,?_⟩
  apply tsub_le_iff_right.mpr
  have hp := initialMarkedWindow_partition s (Real.log (r/(rho*K*(Real.log w)^2)))
    (Real.log (rho/10)) (by rw [hWidth]; exact hH.le)
  calc
    1 = initialMarkedWindowSuccess s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10))+
        initialMarkedWindowFailure s (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) := hp.symm
    _ ≤ _ := add_le_add le_rfl hFailure

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
