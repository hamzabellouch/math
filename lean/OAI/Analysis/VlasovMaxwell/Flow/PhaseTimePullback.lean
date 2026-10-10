import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ArrivalDomain
import OAI.Analysis.VlasovMaxwell.Regularity.PhysicalCutoffCoordinates

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def phaseTimePullback {W : Type*} [Zero W] (α : Phase→ℝ→Phase) (T : ℝ)
    (g : ℝ×Phase→W) : ℝ×Phase→W :=
  (Ioo (0:ℝ) T ×ˢ (univ : Set Phase)).indicator (fun p=>g (p.1,α p.2 p.1))

lemma PhaseFlowOn.measurable_phaseTimePullback {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) {W : Type*} [Zero W] [MeasurableSpace W]
    {g : ℝ×Phase→W} (hg : Measurable g) :
    Measurable (phaseTimePullback F.flow T g) := by
  classical
  have hm := (hg.comp (measurable_fst.prodMk F.measurable_joint_flow_zero)).indicator
    ((measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) T)).prod MeasurableSet.univ)
  convert hm using 1
  funext p
  by_cases hp : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase)
  · simp only [phaseTimePullback,Function.comp_apply,indicator_of_mem hp]
  · simp only [phaseTimePullback,indicator_of_notMem hp]

lemma PhaseFlowOn.lintegral_phaseTimePullback {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) {g : ℝ×Phase→ENNReal} (hg : Measurable g) :
    (∫⁻ p : ℝ×Phase,phaseTimePullback F.flow T g p)=
      ∫⁻ p in Ioo (0:ℝ) T ×ˢ (univ : Set Phase),g p := by
  classical
  have hS := (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) T)).prod (MeasurableSet.univ : MeasurableSet (univ : Set Phase))
  rw [←lintegral_indicator hS]
  calc
    _ = ∫⁻ t : ℝ,∫⁻ z : Phase,phaseTimePullback F.flow T g (t,z) :=
      lintegral_prod _ (F.measurable_phaseTimePullback hg).aemeasurable
    _ = ∫⁻ t : ℝ,∫⁻ z : Phase,(Ioo (0:ℝ) T ×ˢ (univ : Set Phase)).indicator g (t,z) := by
      apply lintegral_congr
      intro t
      by_cases ht : t∈Ioo (0:ℝ) T
      · simpa only [phaseTimePullback,indicator_of_mem (show (t,_)∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase) from ⟨ht,mem_univ _⟩)]
          using F.lintegral_comp (Ioo_subset_Icc_self ht) (fun z=>g (t,z))
      · have hp : ∀z : Phase,(t,z)∉Ioo (0:ℝ) T ×ˢ (univ : Set Phase) := fun z h=>ht h.1
        simp only [phaseTimePullback,indicator_of_notMem (hp _)]
    _ = _ := (lintegral_prod _ (hg.indicator hS).aemeasurable).symm

lemma PhaseFlowOn.phaseTimePullback_integrable_iff {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    {g : ℝ×Phase→W} (hg : Measurable g) :
    Integrable (phaseTimePullback F.flow T g) ↔
      IntegrableOn g (Ioo (0:ℝ) T ×ˢ (univ : Set Phase)) := by
  classical
  have hS := (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) T)).prod (MeasurableSet.univ : MeasurableSet (univ : Set Phase))
  have he : (∫⁻ p : ℝ×Phase,ENNReal.ofReal ‖phaseTimePullback F.flow T g p‖)=
      ∫⁻ p in Ioo (0:ℝ) T ×ˢ (univ : Set Phase),ENNReal.ofReal ‖g p‖ := by
    rw [←F.lintegral_phaseTimePullback hg.norm.ennreal_ofReal]
    apply lintegral_congr
    intro p
    by_cases hp : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase)
    · simp only [phaseTimePullback,indicator_of_mem hp]
    · simp only [phaseTimePullback,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero]
  constructor
  · intro h
    refine ⟨hg.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm,←he]
    exact (hasFiniteIntegral_iff_norm _).mp h.2
  · intro h
    refine ⟨(F.measurable_phaseTimePullback hg).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm,he]
    exact (hasFiniteIntegral_iff_norm _).mp h.2

lemma PhaseFlowOn.integral_phaseTimePullback {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
    {g : ℝ×Phase→W} (hg : Measurable g)
    (hi : IntegrableOn g (Ioo (0:ℝ) T ×ˢ (univ : Set Phase))) :
    (∫ p : ℝ×Phase,phaseTimePullback F.flow T g p)=
      ∫ p in Ioo (0:ℝ) T ×ˢ (univ : Set Phase),g p := by
  classical
  have hS := (measurableSet_Ioo : MeasurableSet (Ioo (0:ℝ) T)).prod (MeasurableSet.univ : MeasurableSet (univ : Set Phase))
  have hip := (F.phaseTimePullback_integrable_iff hg).mpr hi
  have hiS := hi.integrable_indicator hS
  rw [←integral_indicator hS]
  calc
    _ = ∫ t : ℝ,∫ z : Phase,phaseTimePullback F.flow T g (t,z) := integral_prod _ hip
    _ = ∫ t : ℝ,∫ z : Phase,(Ioo (0:ℝ) T ×ˢ (univ : Set Phase)).indicator g (t,z) := by
      apply integral_congr_ae
      apply ae_of_all
      intro t
      by_cases ht : t∈Ioo (0:ℝ) T
      · simpa only [phaseTimePullback,indicator_of_mem (show (t,_)∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase) from ⟨ht,mem_univ _⟩)]
          using F.integral_comp (Ioo_subset_Icc_self ht) (fun z=>g (t,z))
      · have hp : ∀z : Phase,(t,z)∉Ioo (0:ℝ) T ×ˢ (univ : Set Phase) := fun z h=>ht h.1
        simp only [phaseTimePullback,indicator_of_notMem (hp _)]
    _ = _ := (integral_prod _ hiS).symm

lemma PhaseFlowOn.arrival_polar_mem {E B : Field} {T s r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T)
    (hr : r∈Ioo (0:ℝ) (T-s)) (n : Sphere) :
    (s,(F.flow zX (s+r)).1-r • n.1)∈arrivalDomain F.flow zX T := by
  have hn := sphere_norm n
  have hw : r • n.1∈receiverRadialDomain s T := by
    change 0<‖r • n.1‖ ∧ s+‖r • n.1‖<T
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,hn,mul_one]
    exact ⟨hr.1,by linarith [hr.2]⟩
  have him := F.receiver_image (Ioo_subset_Icc_self hs) zX
  have hy : receiverRadial F.flow zX s (r • n.1) ∈
      ball (F.flow zX T).1 (T-s)\{(F.flow zX s).1} := by
    rw [←him]
    exact mem_image_of_mem _ hw
  have he : receiverRadial F.flow zX s (r • n.1)=
      (F.flow zX (s+r)).1-r • n.1 := by
    simp only [receiverRadial,norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,hn,mul_one]
  rw [he] at hy
  refine ⟨hs,?_,?_⟩
  · have hh := hy.1
    rw [mem_ball,dist_eq_norm,norm_sub_rev] at hh
    linarith
  · exact fun hh=>hy.2 (mem_singleton_iff.mpr hh.symm)

lemma PhaseFlowOn.arrival_polar_time {E B : Field} {T s r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T)
    (hr : r∈Ioo (0:ℝ) (T-s)) (n : Sphere) :
    arrivalTime F.flow zX T (s,(F.flow zX (s+r)).1-r • n.1)=s+r := by
  have hd := F.arrival_polar_mem zX hs hr n
  have hl := F.arrivalLabel_mem zX hd
  have hh : F.flow (arrivalLabel F.flow (s,(F.flow zX (s+r)).1-r • n.1)).2 s =
      ((F.flow zX (s+r)).1-r • n.1,0) :=
    F.flow_inversePhase (Ioo_subset_Icc_self hs) _
  symm
  apply F.branch_unique (s:=s) zX _ hl.1 ⟨by linarith [hr.1],by linarith [hr.2]⟩
  rw [hh]
  simp only [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,
    sphere_norm,mul_one]
  ring

lemma PhaseFlowOn.arrival_polar_radius {E B : Field} {T s r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T)
    (hr : r∈Ioo (0:ℝ) (T-s)) (n : Sphere) :
    arrivalRadius F.flow zX T (s,(F.flow zX (s+r)).1-r • n.1)=r := by
  rw [arrivalRadius,F.arrival_polar_time zX hs hr n]
  ring

lemma PhaseFlowOn.arrival_polar_direction {E B : Field} {T s r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T)
    (hr : r∈Ioo (0:ℝ) (T-s)) (n : Sphere) :
    arrivalDirection F.flow zX T (s,(F.flow zX (s+r)).1-r • n.1)=n.1 := by
  rw [arrivalDirection,F.arrival_polar_radius zX hs hr n,F.arrival_polar_time zX hs hr n]
  simp only [sub_sub_cancel,smul_smul,inv_mul_cancel₀ (ne_of_gt hr.1),one_smul]

def arrivalInverseSquare (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Vec→ℝ :=
  (arrivalDomain α zX T).indicator (fun p=>(arrivalRadius α zX T p)⁻¹^2)

lemma PhaseFlowOn.measurable_arrivalInverseSquare {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    Measurable (arrivalInverseSquare F.flow zX T) := by
  classical
  have hc : ContinuousOn (fun p : ℝ×Vec=>(arrivalRadius F.flow zX T p)⁻¹^2)
      (arrivalDomain F.flow zX T) := by
    intro p hp
    apply (((F.arrivalRadius_continuousAt zX hp).inv₀ ?_).pow 2).continuousWithinAt
    exact ne_of_gt (sub_pos.mpr (F.arrival_time_spec zX hp).1.1)
  exact hc.measurable_piecewise continuousOn_const (F.isOpen_arrivalDomain zX).measurableSet

lemma arrivalInverseSquare_nonneg (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (p : ℝ×Vec) : 0≤arrivalInverseSquare α zX T p := by
  classical
  exact indicator_nonneg (fun _ _=>sq_nonneg _) _

lemma PhaseFlowOn.arrivalInverseSquare_lintegral {E B : Field} {T s : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hs : s∈Ioo 0 T) :
    (∫⁻ y : Vec,ENNReal.ofReal (arrivalInverseSquare F.flow zX T (s,y))) ≤
      (2:ENNReal)*ENNReal.ofReal (T-s)*sphereMeasure univ := by
  classical
  let g : Vec→ENNReal := fun y=>ENNReal.ofReal (arrivalInverseSquare F.flow zX T (s,y))
  have hgm : Measurable g := ((F.measurable_arrivalInverseSquare zX).comp
    (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hrestrict : (∫⁻ y : Vec,g y)=∫⁻ y in ball (F.flow zX T).1 (T-s),g y := by
    rw [←lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro y
    by_cases hy : y∈ball (F.flow zX T).1 (T-s)
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      have hh : (s,y)∉arrivalDomain F.flow zX T := by
        intro h
        apply hy
        rw [mem_ball,dist_eq_norm,norm_sub_rev]
        linarith [h.2.1]
      simp only [g,arrivalInverseSquare,indicator_of_notMem hh,ENNReal.ofReal_zero]
  change (∫⁻ y : Vec,g y)≤_
  rw [hrestrict,F.receiver_polar_lintegral (Ioo_subset_Icc_self hs) zX hgm]
  calc
    _ ≤ ∫⁻ _n : Sphere,∫⁻ _r in Ioo (0:ℝ) (T-s),(2:ENNReal) ∂volume ∂sphereMeasure := by
      apply lintegral_mono
      intro n
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem measurableSet_Ioo
      intro r hr
      have hd := F.arrival_polar_mem zX hs hr n
      have hra := F.arrival_polar_radius zX hs hr n
      have hD : 0≤1-dot n.1 (velocity (F.flow zX (s+r)).2) :=
        (cone_denom_pos _ _ (sphere_norm n)).le
      change ENNReal.ofReal (r^2*(1-dot n.1 (velocity (F.flow zX (s+r)).2))) *
        ENNReal.ofReal (arrivalInverseSquare F.flow zX T (s,(F.flow zX (s+r)).1-r • n.1))≤2
      rw [arrivalInverseSquare,indicator_of_mem hd,hra,←ENNReal.ofReal_mul (mul_nonneg (sq_nonneg r) hD)]
      have he : r^2*(1-dot n.1 (velocity (F.flow zX (s+r)).2))*r⁻¹^2=
          1-dot n.1 (velocity (F.flow zX (s+r)).2) := by
        field_simp [ne_of_gt hr.1]
      rw [he]
      exact (ENNReal.ofReal_le_ofReal (real_deficit_le_two (sphere_norm n) _)).trans_eq (by norm_num)
    _ = _ := by simp [lintegral_const,Real.volume_Ioo,mul_assoc]

lemma PhaseFlowOn.arrivalInverseSquare_integrable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    Integrable (arrivalInverseSquare F.flow zX T) := by
  classical
  have hm := F.measurable_arrivalInverseSquare zX
  have hfin : (∫⁻ p : ℝ×Vec,ENNReal.ofReal (arrivalInverseSquare F.flow zX T p))<⊤ := by
    change (∫⁻ p : ℝ×Vec,ENNReal.ofReal (arrivalInverseSquare F.flow zX T p)
      ∂((volume : Measure ℝ).prod (volume : Measure Vec)))<⊤
    rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
    have hr : (∫⁻ s : ℝ,∫⁻ y : Vec,ENNReal.ofReal (arrivalInverseSquare F.flow zX T (s,y)))=
        ∫⁻ s in Ioo (0:ℝ) T,∫⁻ y : Vec,ENNReal.ofReal (arrivalInverseSquare F.flow zX T (s,y)) := by
      rw [←lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro s
      by_cases hs : s∈Ioo (0:ℝ) T
      · rw [indicator_of_mem hs]
      · rw [indicator_of_notMem hs]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro y
        have hh : (s,y)∉arrivalDomain F.flow zX T := fun h=>hs h.1
        simp only [arrivalInverseSquare,indicator_of_notMem hh,ENNReal.ofReal_zero,Pi.zero_apply]
    rw [hr]
    have hb : ∀ s∈Ioo (0:ℝ) T,
        (∫⁻ y : Vec,ENNReal.ofReal (arrivalInverseSquare F.flow zX T (s,y)))≤
          (2:ENNReal)*ENNReal.ofReal T*sphereMeasure univ := by
      intro s hs
      apply (F.arrivalInverseSquare_lintegral zX hs).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (ENNReal.ofReal_le_ofReal (sub_le_self _ hs.1.le)) zero_le) zero_le
    apply lt_of_le_of_lt (lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioo hb))
    change (∫⁻ _s in Ioo (0:ℝ) T,(2:ENNReal)*ENNReal.ofReal T*sphereMeasure univ)<⊤
    simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) (measure_lt_top _ _)) ENNReal.ofReal_lt_top
  refine ⟨hm.aestronglyMeasurable,(hasFiniteIntegral_iff_norm _).mpr ?_⟩
  simpa only [Real.norm_eq_abs,abs_of_nonneg (arrivalInverseSquare_nonneg F.flow zX T _)] using hfin

def phaseArrivalMajorant (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (K : Set Vec) (p : ℝ×Phase) : ℝ :=
  arrivalInverseSquare α zX T (p.1,p.2.1)*K.indicator (fun _=>1) p.2.2

lemma PhaseFlowOn.measurable_phaseArrivalMajorant {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {K : Set Vec} (hK : MeasurableSet K) :
    Measurable (phaseArrivalMajorant F.flow zX T K) :=
  ((F.measurable_arrivalInverseSquare zX).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      ((measurable_const.indicator hK).comp (measurable_snd.comp measurable_snd))

lemma phaseArrivalMajorant_nonneg (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (K : Set Vec) (p : ℝ×Phase) : 0≤phaseArrivalMajorant α zX T K p := by
  exact mul_nonneg (arrivalInverseSquare_nonneg α zX T _)
    (indicator_nonneg (fun _ _=>by norm_num) _)

lemma PhaseFlowOn.phaseArrivalMajorant_integrable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {K : Set Vec} (hK : IsCompact K) :
    Integrable (phaseArrivalMajorant F.flow zX T K) := by
  have hk : Integrable (K.indicator (fun _ : Vec=>(1:ℝ))) :=
    (integrableOn_const hK.measure_lt_top.ne : IntegrableOn (fun _ : Vec=>(1:ℝ)) K).integrable_indicator hK.measurableSet
  have hh := (F.arrivalInverseSquare_integrable zX).mul_prod hk
  have hm := (volume_preserving_prodAssoc (α₁:=ℝ) (β₁:=Vec) (γ₁:=Vec)).symm
  exact hm.integrable_comp_of_integrable hh

lemma PhaseFlowOn.source_cone_integrable_of_bound {E B : Field} {T C : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {K : Set Vec} (hK : IsCompact K)
    {g : ℝ×Phase→Vec} (hg : AEStronglyMeasurable g)
    (hb : ∀ᵐ p,‖g p‖≤C*phaseArrivalMajorant F.flow zX T K p) : Integrable g :=
  ((F.phaseArrivalMajorant_integrable zX hK).const_mul C).mono' hg hb

end RVM

end

end OAI
