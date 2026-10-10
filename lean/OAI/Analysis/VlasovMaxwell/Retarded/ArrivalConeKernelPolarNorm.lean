import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ActualLabelCutoffCost

namespace OAI

noncomputable section

section
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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.arrivalConeKernel_polar_norm {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T))
    (hσ : σ∈Ioo 0 T) :
    (∫⁻z : Phase,ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖)=
      ∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX (σ+r)).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX (σ+r)).1-r • n.1,v)) •
          A ((σ+r,σ),(n.1,((F.flow zX (σ+r)).1-r • n.1,v)))‖ ∂volume ∂volume ∂sphereMeasure := by
  classical
  let g : Vec→ENNReal := fun y=>∫⁻v : Vec,ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,(y,v))‖
  have hm : Measurable (fun z : Phase=>ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖) :=
    (((F.measurable_arrivalConeKernel hs zX hA).comp (measurable_const.prodMk measurable_id)).norm).ennreal_ofReal
  have hg : Measurable g := hm.lintegral_prod_right'
  calc
    _ = ∫⁻y : Vec,g y := lintegral_prod _ hm.aemeasurable
    _ = ∫⁻y in ball (F.flow zX T).1 (T-σ),g y := by
      rw [←lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y∈ball (F.flow zX T).1 (T-σ)
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro v
        have hp : (σ,(y,v))∉arrivalPhaseDomain F.flow zX T := by
          intro hp
          apply hy
          rw [mem_ball,dist_eq_norm,norm_sub_rev]
          linarith [hp.2.1]
        simp only [arrivalConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero,Pi.zero_apply]
    _ = _ := by
      rw [F.receiver_polar_lintegral (Ioo_subset_Icc_self hσ) zX hg]
      apply lintegral_congr
      intro n
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      have hd : 0≤1-dot n.1 (velocity (F.flow zX (σ+r)).2) := (cone_denom_pos _ _ (sphere_norm n)).le
      have he : r^2*(1-dot n.1 (velocity (F.flow zX (σ+r)).2))*r⁻¹^2=
          1-dot n.1 (velocity (F.flow zX (σ+r)).2) := by
        field_simp [hr.1.ne']
      dsimp only [g]
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro v
      have hp : (σ,((F.flow zX (σ+r)).1-r • n.1,v))∈arrivalPhaseDomain F.flow zX T :=
        F.arrival_polar_mem zX hσ hr n
      rw [arrivalConeKernel,indicator_of_mem hp,F.arrival_polar_radius zX hσ hr n]
      simp only [arrivalKernelState,F.arrival_polar_time zX hσ hr n,F.arrival_polar_direction zX hσ hr n,
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (r⁻¹))]
      rw [ENNReal.ofReal_mul (sq_nonneg (r⁻¹)),←mul_assoc,
        ←ENNReal.ofReal_mul (mul_nonneg (sq_nonneg r) hd),he]

lemma PhaseFlowOn.lintegral_norm_labelConeKernel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻σ in Ioo (0:ℝ) T,∫⁻z : Phase,ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖ := by
  classical
  have hm := (F.measurable_arrivalConeKernel hs zX hA).norm.ennreal_ofReal
  rw [F.labelConeKernel_eq_pullback hs zX]
  have he : (fun p : ℝ×Phase=>ENNReal.ofReal ‖phaseTimePullback F.flow T (arrivalConeKernel s F.flow zX T A) p‖)=
      phaseTimePullback F.flow T (fun p=>ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A p‖) := by
    funext p
    by_cases hp : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase)
    · simp only [phaseTimePullback,indicator_of_mem hp]
    · simp only [phaseTimePullback,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero]
  rw [he,F.lintegral_phaseTimePullback hm]
  change (∫⁻ p,ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A p‖
    ∂((volume : Measure ℝ).prod (volume : Measure Phase)).restrict (Ioo 0 T ×ˢ univ)) = _
  rw [←Measure.restrict_prod_eq_prod_univ]
  exact lintegral_prod _ hm.aemeasurable

lemma PhaseFlowOn.labelConeKernel_polar_norm {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻σ in Ioo (0:ℝ) T,∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX (σ+r)).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX (σ+r)).1-r • n.1,v)) •
          A ((σ+r,σ),(n.1,((F.flow zX (σ+r)).1-r • n.1,v)))‖ ∂volume ∂volume ∂sphereMeasure := by
  rw [F.lintegral_norm_labelConeKernel hs zX hA]
  exact setLIntegral_congr_fun measurableSet_Ioo (fun σ hσ=>F.arrivalConeKernel_polar_norm hs zX hA hσ)

lemma PhaseFlowOn.labelConeKernel_triangle_norm {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T)) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure := by
  let X := prefixFlow F.flow T zX
  have hc : Continuous (prefixClamp T) := continuous_const.max (continuous_const.min continuous_id)
  have hX : Continuous X := (F.continuousOn_time zX).comp_continuous hc (prefixClamp_mem hT)
  let S : (ℝ×ℝ×Sphere)×Vec → ConeKernelState := fun p=>
    ((prefixClamp T p.1.1,prefixClamp T p.1.2.1),
      (p.1.2.2.1,((X p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))
  have hS : Continuous S := by dsimp [S]; fun_prop
  have hSA : Continuous (fun p=>A (S p)) := hA.comp_continuous hS (fun p=>
    ⟨⟨prefixClamp_mem hT _,prefixClamp_mem hT _⟩,⟨p.1.2.2.2,mem_univ _⟩⟩)
  have hSf : Continuous (fun p=>s.f ((S p).1.2,(S p).2.2)) :=
    hs.f_smooth.continuousOn.comp_continuous (hS.fst.snd.prodMk hS.snd.snd)
      (fun p=>⟨prefixClamp_mem hT _,mem_univ _⟩)
  let f : ℝ×ℝ×Sphere → ENNReal := fun p=>
    ENNReal.ofReal (1-dot p.2.2.1 (velocity (X p.1).2))*
      ∫⁻v : Vec,ENNReal.ofReal ‖s.f ((S (p,v)).1.2,(S (p,v)).2.2) • A (S (p,v))‖
  have hD : Continuous (fun p : ℝ×ℝ×Sphere=>1-dot p.2.2.1 (velocity (X p.1).2)) := by
    simp only [dot_eq_inner]
    exact continuous_const.sub ((continuous_subtype_val.comp continuous_snd.snd).inner
      ((contDiff_velocity (k:=1)).continuous.comp (hX.comp continuous_fst).snd))
  have hf : Measurable f := hD.measurable.ennreal_ofReal.mul
    ((hSf.smul hSA).norm.measurable.ennreal_ofReal.lintegral_prod_right')
  have he : ∀t∈Icc 0 T,∀σ∈Icc 0 T,∀n : Sphere,
      f (t,σ,n)=ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ := by
    intro t ht σ hσ n
    simp only [f,S,X,prefixFlow,prefixClamp_eq ht,prefixClamp_eq hσ]
  rw [F.labelConeKernel_polar_norm hs zX hA]
  calc
    _ = ∫⁻σ in Ioo (0:ℝ) T,∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),f (σ+r,σ,n) ∂volume ∂sphereMeasure := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      apply lintegral_congr
      intro n
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [he _ ⟨by linarith [hσ.1,hr.1],by linarith [hr.2]⟩ _ (Ioo_subset_Icc_self hσ)]
      simp only [add_sub_cancel_left]
    _ = ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,f (t,σ,n) ∂sphereMeasure :=
      lintegral_retarded_triangle_parameter sphereMeasure T hf
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      exact lintegral_congr (fun n=>he _ (Ioo_subset_Icc_self ht) _ ⟨hσ.1.le,hσ.2.le.trans ht.2.le⟩ n)

end RVM

end

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

def arrivalReceiverTime (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) (p : ℝ×Phase) : ℝ :=
  (arrivalDomain α zX T).indicator (arrivalTime α zX T) (p.1,p.2.1)

lemma PhaseFlowOn.arrivalReceiverTime_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    Measurable (arrivalReceiverTime F.flow zX T) :=
  (F.measurable_arrival_zero zX).comp (measurable_fst.prodMk measurable_snd.fst)

lemma PhaseFlowOn.arrivalReceiverTime_polar {E B : Field} {T σ r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (hσ : σ∈Ioo 0 T)
    (hr : r∈Ioo 0 (T-σ)) (n : Sphere) (v : Vec) :
    arrivalReceiverTime F.flow zX T (σ,((F.flow zX (σ+r)).1-r • n.1,v))=σ+r := by
  classical
  rw [arrivalReceiverTime,indicator_of_mem (F.arrival_polar_mem zX hσ hr n :
    (σ,((F.flow zX (σ+r)).1-r • n.1,v))∈arrivalPhaseDomain F.flow zX T),
    F.arrival_polar_time zX hσ hr n]

lemma PhaseFlowOn.lintegral_weighted_labelConeKernel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T))
    {b : ℝ→ℝ} (hb : Measurable b) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T p))*ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻σ in Ioo (0:ℝ) T,∫⁻z : Phase,
        ENNReal.ofReal (b (arrivalReceiverTime F.flow zX T (σ,z)))*ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖ := by
  classical
  let g : ℝ×Phase→ENNReal := fun p=>ENNReal.ofReal (b (arrivalReceiverTime F.flow zX T p))*ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A p‖
  have hg : Measurable g := (hb.comp (F.arrivalReceiverTime_measurable zX)).ennreal_ofReal.mul
    (F.measurable_arrivalConeKernel hs zX hA).norm.ennreal_ofReal
  have he : (fun p=>ENNReal.ofReal (b (labelReceiverTime F.flow zX T p))*ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      phaseTimePullback F.flow T g := by
    funext p
    by_cases hp : p∈labelBranchDomain F.flow zX T
    · have ha := (labelBranchDomain_iff _ _ _ _).mp hp
      have ht : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase) := ⟨hp.1.1,mem_univ _⟩
      have ha' : (p.1,(F.flow p.2 p.1).1)∈arrivalDomain F.flow zX T := ha
      rw [F.labelConeKernel_eq_pullback hs zX]
      simp only [phaseTimePullback,indicator_of_mem ht,g,labelReceiverTime,indicator_of_mem hp,
        arrivalReceiverTime,indicator_of_mem ha',F.arrivalTime_flow_eq_branchTime zX p.2 hp]
    · have ha := mt (labelBranchDomain_iff _ _ _ _).mpr hp
      rw [labelConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero,mul_zero]
      by_cases ht : p∈Ioo (0:ℝ) T ×ˢ (univ : Set Phase)
      · simp only [phaseTimePullback,indicator_of_mem ht,g,arrivalConeKernel,indicator_of_notMem ha,
          norm_zero,ENNReal.ofReal_zero,mul_zero]
      · simp only [phaseTimePullback,indicator_of_notMem ht]
  rw [he,F.lintegral_phaseTimePullback hg]
  change (∫⁻p,g p ∂((volume : Measure ℝ).prod (volume : Measure Phase)).restrict (Ioo 0 T ×ˢ univ))=_
  rw [←Measure.restrict_prod_eq_prod_univ]
  exact lintegral_prod _ hg.aemeasurable

lemma PhaseFlowOn.arrivalConeKernel_polar_weighted_norm {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T))
    (hσ : σ∈Ioo 0 T) {b : ℝ→ℝ} (hb : Measurable b) :
    (∫⁻z : Phase,ENNReal.ofReal (b (arrivalReceiverTime F.flow zX T (σ,z)))*ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖)=
      ∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),
        ENNReal.ofReal (b (σ+r))*ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX (σ+r)).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX (σ+r)).1-r • n.1,v)) •
          A ((σ+r,σ),(n.1,((F.flow zX (σ+r)).1-r • n.1,v)))‖ ∂volume ∂volume ∂sphereMeasure := by
  classical
  let g : Vec→ENNReal := fun y=>∫⁻v : Vec,ENNReal.ofReal (b (arrivalReceiverTime F.flow zX T (σ,(y,v))))*ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,(y,v))‖
  have hm : Measurable (fun z : Phase=>ENNReal.ofReal (b (arrivalReceiverTime F.flow zX T (σ,z)))*ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖) :=
    (hb.comp ((F.arrivalReceiverTime_measurable zX).comp (measurable_const.prodMk measurable_id))).ennreal_ofReal.mul
      (((F.measurable_arrivalConeKernel hs zX hA).comp (measurable_const.prodMk measurable_id)).norm).ennreal_ofReal
  have hg : Measurable g := hm.lintegral_prod_right'
  calc
    _ = ∫⁻y : Vec,g y := lintegral_prod _ hm.aemeasurable
    _ = ∫⁻y in ball (F.flow zX T).1 (T-σ),g y := by
      rw [←lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y∈ball (F.flow zX T).1 (T-σ)
      · rw [indicator_of_mem hy]
      · rw [indicator_of_notMem hy]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro v
        have hp : (σ,(y,v))∉arrivalPhaseDomain F.flow zX T := by
          intro hp
          apply hy
          rw [mem_ball,dist_eq_norm,norm_sub_rev]
          linarith [hp.2.1]
        simp only [arrivalConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero,Pi.zero_apply,mul_zero]
    _ = _ := by
      rw [F.receiver_polar_lintegral (Ioo_subset_Icc_self hσ) zX hg]
      apply lintegral_congr
      intro n
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      have hd : 0≤1-dot n.1 (velocity (F.flow zX (σ+r)).2) := (cone_denom_pos _ _ (sphere_norm n)).le
      have he : r^2*(1-dot n.1 (velocity (F.flow zX (σ+r)).2))*r⁻¹^2=
          1-dot n.1 (velocity (F.flow zX (σ+r)).2) := by
        field_simp [hr.1.ne']
      dsimp only [g]
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ←lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
      apply lintegral_congr
      intro v
      have hp : (σ,((F.flow zX (σ+r)).1-r • n.1,v))∈arrivalPhaseDomain F.flow zX T :=
        F.arrival_polar_mem zX hσ hr n
      rw [F.arrivalReceiverTime_polar zX hσ hr n v,arrivalConeKernel,indicator_of_mem hp,F.arrival_polar_radius zX hσ hr n]
      simp only [arrivalKernelState,F.arrival_polar_time zX hσ hr n,F.arrival_polar_direction zX hσ hr n,
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (r⁻¹))]
      rw [ENNReal.ofReal_mul (sq_nonneg (r⁻¹))]
      calc
        _ = ENNReal.ofReal (b (σ+r))*((ENNReal.ofReal (r^2*(1-dot n.1 (velocity (F.flow zX (σ+r)).2)))*ENNReal.ofReal (r⁻¹^2))*
            ENNReal.ofReal ‖s.f (σ,((F.flow zX (σ+r)).1-r • n.1,v)) •
              A ((σ+r,σ),(n.1,((F.flow zX (σ+r)).1-r • n.1,v)))‖) := by simp only [norm_smul,Real.norm_eq_abs]; ac_rfl
        _ = _ := by
          rw [←ENNReal.ofReal_mul (mul_nonneg (sq_nonneg r) hd),he]
          simp only [norm_smul,Real.norm_eq_abs]
          ac_rfl

lemma PhaseFlowOn.labelConeKernel_polar_weighted_norm {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T))
    {b : ℝ→ℝ} (hb : Measurable b) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T p))*ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻σ in Ioo (0:ℝ) T,∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),
        ENNReal.ofReal (b (σ+r))*ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX (σ+r)).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX (σ+r)).1-r • n.1,v)) •
          A ((σ+r,σ),(n.1,((F.flow zX (σ+r)).1-r • n.1,v)))‖ ∂volume ∂volume ∂sphereMeasure := by
  rw [F.lintegral_weighted_labelConeKernel hs zX hA hb]
  exact setLIntegral_congr_fun measurableSet_Ioo (fun σ hσ=>F.arrivalConeKernel_polar_weighted_norm hs zX hA hσ hb)

lemma PhaseFlowOn.labelConeKernel_triangle_weighted_norm {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T))
    {b : ℝ→ℝ} (hb : Measurable b) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T p))*ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (b t)*ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure := by
  let X := prefixFlow F.flow T zX
  have hc : Continuous (prefixClamp T) := continuous_const.max (continuous_const.min continuous_id)
  have hX : Continuous X := (F.continuousOn_time zX).comp_continuous hc (prefixClamp_mem hT)
  let S : (ℝ×ℝ×Sphere)×Vec → ConeKernelState := fun p=>
    ((prefixClamp T p.1.1,prefixClamp T p.1.2.1),
      (p.1.2.2.1,((X p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))
  have hS : Continuous S := by dsimp [S]; fun_prop
  have hSA : Continuous (fun p=>A (S p)) := hA.comp_continuous hS (fun p=>
    ⟨⟨prefixClamp_mem hT _,prefixClamp_mem hT _⟩,⟨p.1.2.2.2,mem_univ _⟩⟩)
  have hSf : Continuous (fun p=>s.f ((S p).1.2,(S p).2.2)) :=
    hs.f_smooth.continuousOn.comp_continuous (hS.fst.snd.prodMk hS.snd.snd)
      (fun p=>⟨prefixClamp_mem hT _,mem_univ _⟩)
  let f : ℝ×ℝ×Sphere → ENNReal := fun p=>
    ENNReal.ofReal (b p.1)*ENNReal.ofReal (1-dot p.2.2.1 (velocity (X p.1).2))*
      ∫⁻v : Vec,ENNReal.ofReal ‖s.f ((S (p,v)).1.2,(S (p,v)).2.2) • A (S (p,v))‖
  have hD : Continuous (fun p : ℝ×ℝ×Sphere=>1-dot p.2.2.1 (velocity (X p.1).2)) := by
    simp only [dot_eq_inner]
    exact continuous_const.sub ((continuous_subtype_val.comp continuous_snd.snd).inner
      ((contDiff_velocity (k:=1)).continuous.comp (hX.comp continuous_fst).snd))
  have hf : Measurable f := ((hb.comp measurable_fst).ennreal_ofReal.mul hD.measurable.ennreal_ofReal).mul
    ((hSf.smul hSA).norm.measurable.ennreal_ofReal.lintegral_prod_right')
  have he : ∀t∈Icc 0 T,∀σ∈Icc 0 T,∀n : Sphere,
      f (t,σ,n)=ENNReal.ofReal (b t)*ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ := by
    intro t ht σ hσ n
    simp only [f,S,X,prefixFlow,prefixClamp_eq ht,prefixClamp_eq hσ]
  rw [F.labelConeKernel_polar_weighted_norm hs zX hA hb]
  calc
    _ = ∫⁻σ in Ioo (0:ℝ) T,∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),f (σ+r,σ,n) ∂volume ∂sphereMeasure := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      apply lintegral_congr
      intro n
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [he _ ⟨by linarith [hσ.1,hr.1],by linarith [hr.2]⟩ _ (Ioo_subset_Icc_self hσ)]
      simp only [add_sub_cancel_left]
    _ = ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,f (t,σ,n) ∂sphereMeasure :=
      lintegral_retarded_triangle_parameter sphereMeasure T hf
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      exact lintegral_congr (fun n=>he _ (Ioo_subset_Icc_self ht) _ ⟨hσ.1.le,hσ.2.le.trans ht.2.le⟩ n)

end RVM

end

end OAI
