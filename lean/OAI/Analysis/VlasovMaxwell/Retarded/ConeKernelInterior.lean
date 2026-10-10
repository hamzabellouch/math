import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.ActualLabelCutoffCost

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.measurable_arrivalConeKernel_borel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : Measurable A) :
    Measurable (arrivalConeKernel s F.flow zX T A) := by
  classical
  let D := arrivalPhaseDomain F.flow zX T
  have hD : MeasurableSet D := (F.isOpen_arrivalPhaseDomain zX).measurableSet
  have hr : ContinuousOn (fun p : ℝ×Phase=>(arrivalRadius F.flow zX T (p.1,p.2.1))⁻¹^2) D := by
    apply ContinuousOn.pow
    apply ContinuousOn.inv₀
    · intro p hp
      exact ((F.arrivalRadius_continuousAt zX hp).comp (f := fun p : ℝ×Phase=>(p.1,p.2.1))
        (continuousAt_fst.prodMk continuousAt_snd.fst)).continuousWithinAt
    · intro p hp
      exact (sub_pos.mpr (F.arrival_time_spec zX hp).1.1).ne'
  have hf : ContinuousOn s.f D :=
    hs.f_smooth.continuousOn.mono (fun _ hp=>⟨Ioo_subset_Icc_self hp.1,mem_univ _⟩)
  have hR : Measurable (D.indicator (fun p : ℝ×Phase=>(arrivalRadius F.flow zX T (p.1,p.2.1))⁻¹^2)) :=
    hr.measurable_piecewise continuousOn_const hD
  have hF : Measurable (D.indicator s.f) := hf.measurable_piecewise continuousOn_const hD
  have hS : Measurable (D.indicator (arrivalKernelState F.flow zX T)) :=
    (F.arrivalKernelState_continuousOn zX).measurable_piecewise continuousOn_const hD
  convert hR.smul (hF.smul (hA.comp hS)) using 1
  funext p
  change D.indicator (fun p=>(arrivalRadius F.flow zX T (p.1,p.2.1))⁻¹^2 •
      (s.f p • A (arrivalKernelState F.flow zX T p))) p=
    (D.indicator (fun p : ℝ×Phase=>(arrivalRadius F.flow zX T (p.1,p.2.1))⁻¹^2) p) •
      ((D.indicator s.f p) • A (D.indicator (arrivalKernelState F.flow zX T) p))
  by_cases hp : p∈D
  · simp only [indicator_of_mem hp]
  · simp only [indicator_of_notMem hp,zero_smul]

lemma PhaseFlowOn.arrivalConeKernel_polar_norm_borel {s : Solution} {T σ : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : Measurable A)
    (hσ : σ∈Ioo 0 T) :
    (∫⁻z : Phase,ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖)=
      ∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX (σ+r)).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX (σ+r)).1-r • n.1,v)) •
          A ((σ+r,σ),(n.1,((F.flow zX (σ+r)).1-r • n.1,v)))‖ ∂volume ∂volume ∂sphereMeasure := by
  classical
  let g : Vec→ENNReal := fun y=>∫⁻v : Vec,ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,(y,v))‖
  have hm : Measurable (fun z : Phase=>ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖) :=
    (((F.measurable_arrivalConeKernel_borel hs zX hA).comp (measurable_const.prodMk measurable_id)).norm).ennreal_ofReal
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

lemma PhaseFlowOn.lintegral_norm_labelConeKernel_borel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : Measurable A) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻σ in Ioo (0:ℝ) T,∫⁻z : Phase,ENNReal.ofReal ‖arrivalConeKernel s F.flow zX T A (σ,z)‖ := by
  classical
  have hm := (F.measurable_arrivalConeKernel_borel hs zX hA).norm.ennreal_ofReal
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

lemma PhaseFlowOn.labelConeKernel_polar_norm_borel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : Measurable A) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻σ in Ioo (0:ℝ) T,∫⁻n : Sphere,∫⁻r in Ioo (0:ℝ) (T-σ),
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX (σ+r)).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX (σ+r)).1-r • n.1,v)) •
          A ((σ+r,σ),(n.1,((F.flow zX (σ+r)).1-r • n.1,v)))‖ ∂volume ∂volume ∂sphereMeasure := by
  rw [F.lintegral_norm_labelConeKernel_borel hs zX hA]
  exact setLIntegral_congr_fun measurableSet_Ioo (fun σ hσ=>F.arrivalConeKernel_polar_norm_borel hs zX hA hσ)

lemma PhaseFlowOn.labelConeKernel_triangle_norm_borel {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : Measurable A) :
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
  have hSA : Measurable (fun p=>A (S p)) := hA.comp hS.measurable
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
    ((hSf.measurable.smul hSA).norm.ennreal_ofReal.lintegral_prod_right')
  have he : ∀t∈Icc 0 T,∀σ∈Icc 0 T,∀n : Sphere,
      f (t,σ,n)=ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ := by
    intro t ht σ hσ n
    simp only [f,S,X,prefixFlow,prefixClamp_eq ht,prefixClamp_eq hσ]
  rw [F.labelConeKernel_polar_norm_borel hs zX hA]
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

def coneKernelInterior (T : ℝ) : Set ConeKernelState :=
  coneKernelDomain T ∩ {p | p.1.2<p.1.1}

lemma measurableSet_coneKernelInterior (T : ℝ) : MeasurableSet (coneKernelInterior T) :=
  (((measurableSet_Icc.prod measurableSet_Icc).prod
    (isClosed_sphere.measurableSet.prod MeasurableSet.univ))).inter
      (isOpen_lt continuous_fst.snd continuous_fst.fst).measurableSet

lemma PhaseFlowOn.labelKernelState_mem_interior {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈labelBranchDomain F.flow zX T) :
    labelKernelState F.flow zX T p∈coneKernelInterior T := by
  have ha := (labelBranchDomain_iff _ _ _ _).mp hp
  rw [F.labelKernelState_eq_arrival zX hp]
  exact ⟨F.arrivalKernelState_mem zX ha,(F.arrival_time_spec zX ha).1.1⟩

lemma PhaseFlowOn.labelConeKernel_interior_indicator {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (A : ConeKernelState→Vec) :
    labelConeKernel s F.flow zX T ((coneKernelInterior T).indicator A)=
      labelConeKernel s F.flow zX T A := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · simp only [labelConeKernel,indicator_of_mem hp,
      indicator_of_mem (F.labelKernelState_mem_interior zX hp)]
  · simp only [labelConeKernel,indicator_of_notMem hp]

lemma PhaseFlowOn.labelConeKernel_triangle_norm_interior {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T)) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖labelConeKernel s F.flow zX T A p‖)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure := by
  classical
  have hm : Measurable ((coneKernelInterior T).indicator A) :=
    hA.measurable_piecewise continuousOn_const (measurableSet_coneKernelInterior T)
  rw [←F.labelConeKernel_interior_indicator zX A,
    F.labelConeKernel_triangle_norm_borel hs hT zX hm]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro σ hσ
  apply lintegral_congr
  intro n
  congr 1
  apply lintegral_congr
  intro v
  have hp : ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))∈coneKernelInterior T :=
    ⟨⟨⟨Ioo_subset_Icc_self ht,⟨hσ.1.le,(hσ.2.trans ht.2).le⟩⟩,
      ⟨n.2,mem_univ _⟩⟩,hσ.2⟩
  rw [indicator_of_mem hp]

def coneCutoffState (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : CutoffState :=
  (p.1.1-p.1.2,p.2.1,p.2.2.2,(α zX p.1.1).2)

def coneCutoffRate (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : CutoffState :=
  let a := velocity (α zX p.1.1).2
  let u := velocity p.2.2.2
  let n := p.2.1
  let ρ := (1-dot n u)/(1-dot n a)
  (ρ-1,(p.1.1-p.1.2)⁻¹ • coneMotion a u n,
    (lorentzField s.E s.B (p.1.2,p.2.2)).2,
    ρ • (lorentzField s.E s.B (p.1.1,α zX p.1.1)).2)

def normalisedSelectedCutoff (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (p : ConeKernelState) : Vec :=
  fderiv ℝ (stateCutoff T Q) (coneCutoffState α zX p) (coneCutoffRate s α zX p) •
    normalisedPrimitive (p.1.1-p.1.2) (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1

lemma PhaseFlowOn.coneCutoffState_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (coneCutoffState F.flow zX) (coneKernelInterior T) := by
  exact (continuous_fst.fst.sub continuous_fst.snd).continuousOn.prodMk
    (continuous_snd.fst.continuousOn.prodMk (continuous_snd.snd.snd.continuousOn.prodMk
      (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1.1)).snd)))

lemma PhaseFlowOn.coneCutoffRate_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneCutoffRate s F.flow zX) (coneKernelInterior T) := by
  let S := coneKernelInterior T
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2) S :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn
      (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1.1)).snd)
  have hu : ContinuousOn (fun p : ConeKernelState=>velocity p.2.2.2) S :=
    ((contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd).continuousOn
  have hn : ContinuousOn (fun p : ConeKernelState=>p.2.1) S := continuous_snd.fst.continuousOn
  have hD : ∀p∈S,1-dot p.2.1 (velocity (F.flow zX p.1.1).2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.1.2.1)).ne'
  have hρ : ContinuousOn (fun p : ConeKernelState=>
      (1-dot p.2.1 (velocity p.2.2.2))/(1-dot p.2.1 (velocity (F.flow zX p.1.1).2))) S := by
    simp only [dot_eq_inner] at hD ⊢
    exact (continuousOn_const.sub (hn.inner hu)).div (continuousOn_const.sub (hn.inner ha)) hD
  have hN := (hρ.smul (ha.sub hn)).add hn |>.sub hu
  have hr := (continuous_fst.fst.sub continuous_fst.snd).continuousOn.inv₀
    (show ∀p∈S,p.1.1-p.1.2≠0 from fun _ hp=>(sub_pos.mpr hp.2).ne')
  have hKY : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.2,p.2.2)).2) S :=
    hs.continuousOn_momentumForce.comp (continuous_fst.snd.prodMk continuous_snd.snd).continuousOn
      (fun _ hp=>⟨hp.1.1.2,mem_univ _⟩)
  have hKX : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.1,F.flow zX p.1.1)).2) S :=
    (F.momentumForce_continuousOn_closed hs zX).comp continuous_fst.fst.continuousOn
      (fun _ hp=>hp.1.1.1)
  exact (hρ.sub continuousOn_const).prodMk ((hr.smul hN).prodMk (hKY.prodMk (hρ.smul hKX)))

lemma PhaseFlowOn.normalisedSelectedCutoff_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    ContinuousOn (normalisedSelectedCutoff s F.flow zX T Q) (coneKernelInterior T) := by
  have hz := F.coneCutoffState_continuousOn zX
  have hder : ContinuousOn (fun p=>fderiv ℝ (stateCutoff T Q) (coneCutoffState F.flow zX p))
      (coneKernelInterior T) := by
    intro p hp
    exact ((contDiffAt_stateCutoff T Q (z:=coneCutoffState F.flow zX p)
      (sub_pos.mpr hp.2) (by simpa only [coneCutoffState,mem_sphere,dist_zero_right] using hp.1.2.1)).continuousAt_fderiv
        (by simp)).comp_continuousWithinAt (hz p hp)
  exact (hder.clm_apply (F.coneCutoffRate_continuousOn hs zX)).smul
    ((F.normalised_primitive_continuousOn zX).mono inter_subset_left)

lemma PhaseFlowOn.actualLabelCutoffCost_eq_normalised {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    actualLabelCutoffCost s F.flow zX T Q=
      labelConeKernel s F.flow zX T (normalisedSelectedCutoff s F.flow zX T Q) := by
  classical
  funext p
  rw [actualLabelCutoffCost,F.actualLabelPrimitive_eq_normalised zX]
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hj : p∈jointBranchDomain F.flow zX T := hp
    rw [indicator_of_mem hj]
    simp only [labelConeKernel,indicator_of_mem hp]
    change _= (branchTime F.flow zX p.2 T p.1-p.1)⁻¹^2 •
      (s.f (0,p.2) • normalisedSelectedCutoff s F.flow zX T Q (labelKernelState F.flow zX T p))
    simp only [normalisedSelectedCutoff,coneCutoffState,coneCutoffRate,labelKernelState,
      branchSelectedRate,branchCutoffState,branchCutoffStateRate,branchRate,branchDirection]
    module
  · have hj : p∉jointBranchDomain F.flow zX T := hp
    simp only [indicator_of_notMem hj,labelConeKernel,indicator_of_notMem hp,zero_smul]

lemma PhaseFlowOn.actualLabelCutoffCost_polar_norm {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖actualLabelCutoffCost s F.flow zX T Q p‖)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          normalisedSelectedCutoff s F.flow zX T Q
            ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure := by
  rw [F.actualLabelCutoffCost_eq_normalised zX Q]
  exact F.labelConeKernel_triangle_norm_interior hs hT zX
    (F.normalisedSelectedCutoff_continuousOn hs zX Q)

end RVM

end

end OAI
