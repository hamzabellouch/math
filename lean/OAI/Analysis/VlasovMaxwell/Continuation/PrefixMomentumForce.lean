import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.AngularBump

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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

def prefixMomentumForce (s : Solution) (α : Phase→ℝ→Phase) (T : ℝ) (z : Phase) (t : ℝ) : Vec :=
  (lorentzField s.E s.B (prefixClamp T t,prefixFlow α T z t)).2

lemma PhaseFlowOn.continuous_prefixMomentumForce {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (z : Phase) :
    Continuous (prefixMomentumForce s F.flow T z) := by
  have hα : Continuous (prefixFlow F.flow T z) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have ht : Continuous (prefixClamp T) := continuous_const.max (continuous_const.min continuous_id)
  have hZ := ht.prodMk hα.fst
  have hE := hs.E_smooth.continuousOn.comp_continuous hZ (fun t=>⟨prefixClamp_mem hT t,mem_univ _⟩)
  have hB := hs.B_smooth.continuousOn.comp_continuous hZ (fun t=>⟨prefixClamp_mem hT t,mem_univ _⟩)
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp (((contDiff_velocity (k:=1)).continuous.comp hα.snd).prodMk hB))

lemma PhaseFlowOn.prefixMomentum_hasDerivAt {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) (ht : t∈Ioo 0 T) :
    HasDerivAt (fun r=>(prefixFlow F.flow T z r).2)
      (lorentzField E B (t,F.flow z t)).2 t := by
  have hd : HasDerivAt (fun r=>(F.flow z r).2) (lorentzField E B (t,F.flow z t)).2 t :=
    ((F.ode z t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).snd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  simp only [prefixFlow,prefixClamp_eq hr]

def prefixAngularMultiplier (_s : Solution) (α : Phase→ℝ→Phase) (T w : ℝ)
    (hw : 0<w) (z : Phase) (t : ℝ) : Vec→L[ℝ]Vec :=
  extendedAngularCLM w hw (prefixFlow α T z t).2

def prefixAngularRate (s : Solution) (α : Phase→ℝ→Phase) (T w : ℝ)
    (hw : 0<w) (z : Phase) (t : ℝ) : Vec→L[ℝ]Vec :=
  fderiv ℝ (extendedAngularCLM w hw) (prefixFlow α T z t).2
    (prefixMomentumForce s α T z t)

lemma PhaseFlowOn.prefixAngular_regular {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (hw : 0<w) (z : Phase) :
    Continuous (prefixAngularMultiplier s F.flow T w hw z) ∧
    Continuous (prefixAngularRate s F.flow T w hw z) ∧
    ∀t∈Ioo 0 T,HasDerivAt (prefixAngularMultiplier s F.flow T w hw z)
      (prefixAngularRate s F.flow T w hw z t) t := by
  have hV : Continuous (fun t=>(prefixFlow F.flow T z t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd
  have hd := extendedAngularCLM_contDiff w hw
  refine ⟨hd.continuous.comp hV,(hd.continuous_fderiv (by simp)).comp hV |>.clm_apply
    (F.continuous_prefixMomentumForce hs hT z),?_⟩
  intro t ht
  change HasDerivAt (fun r=>extendedAngularCLM w hw (prefixFlow F.flow T z r).2)
    (fderiv ℝ (extendedAngularCLM w hw) (prefixFlow F.flow T z t).2
      (prefixMomentumForce s F.flow T z t)) t
  have he : prefixMomentumForce s F.flow T z t=(lorentzField s.E s.B (t,F.flow z t)).2 := by
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht)]
  rw [he]
  exact hasDerivAt_extendedAngularCLM (F.prefixMomentum_hasDerivAt z ht) w hw

lemma prefixAngular_highband {s : Solution} {α : Phase→ℝ→Phase} {T t w : ℝ}
    (hw : 0<w) (z : Phase) (ht : t∈Icc 0 T) (hv : w/16≤‖(α z t).2‖) :
    prefixAngularMultiplier s α T w hw z t=angularMultiplierCLM w (α z t).2 ∧
    prefixAngularRate s α T w hw z t=angularDerivativeCLM w (α z t).2
      (lorentzField s.E s.B (t,α z t)).2 := by
  have hnorm : w/32<‖(α z t).2‖ := by linarith
  simp only [prefixAngularMultiplier,prefixAngularRate,prefixMomentumForce,prefixFlow,prefixClamp_eq ht]
  exact ⟨extendedAngularCLM_eq w hw hnorm.le,extendedAngularCLM_fderiv w hw hnorm _⟩

end RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma physicalBinMeasure_receiver_weight {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) {φ : ℝ}
    (hφ : 0≤φ) (hD : B.Dmax≤8*φ^2) {g : ℝ→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)≤
      (∫⁻t in J,g t)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) := by
  let A : Set ConeCoordinate := {z | z.1∈J ∧
    z.2.1∈Icc (z.1-B.rmax) (z.1-B.rmin) ∧
    ‖z.2.2.1-velocity (V z.1)‖≤4*φ}
  have hA : MeasurableSet A := by
    exact (hJ.preimage measurable_fst).inter
      (((measurableSet_le (measurable_fst.sub_const _) (measurable_fst.comp measurable_snd)).inter
        (measurableSet_le (measurable_fst.comp measurable_snd) (measurable_fst.sub_const _))).inter
      (measurableSet_le (((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).sub
        ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst))).norm) measurable_const))
  have hsub : physicalBinBase V B J⊆A := by
    intro z hz
    refine ⟨hz.1,⟨by linarith [hz.2.2.1.2],by linarith [hz.2.2.1.1]⟩,?_⟩
    apply norm_sub_le_of_deficit (sphere_norm z.2.2).le (norm_velocity_lt_one _).le (by positivity)
    nlinarith [hz.2.2.2.2.2]
  have hm : (∫⁻z : ConeCoordinate,A.indicator (fun z=>g z.1) z ∂volume.prod (volume.prod sphereMeasure))=
      ∫⁻t in J,g t*(ENNReal.ofReal (B.rmax-B.rmin)*
        sphereMeasure {n : Sphere | ‖n.1-velocity (V t)‖≤4*φ}) := by
    have hmg : Measurable (A.indicator (fun z : ConeCoordinate=>g z.1)) :=
      (hg.comp measurable_fst).indicator hA
    rw [lintegral_prod _ hmg.aemeasurable,←lintegral_indicator hJ]
    apply lintegral_congr
    intro t
    by_cases ht : t∈J
    · rw [indicator_of_mem ht]
      have he : (fun p : ℝ×Sphere=>A.indicator (fun z=>g z.1) (t,p))=
          ((Icc (t-B.rmax) (t-B.rmin))×ˢ{n : Sphere | ‖n.1-velocity (V t)‖≤4*φ}).indicator
            (fun _=>g t) := by
        funext p
        simp [A,ht,indicator]
      change (∫⁻p : ℝ×Sphere,A.indicator (fun z=>g z.1) (t,p) ∂volume.prod sphereMeasure)=_
      rw [he,lintegral_indicator]
      · rw [lintegral_const,Measure.restrict_apply_univ,Measure.prod_prod,Real.volume_Icc]
        congr 2
        ring_nf
      · exact measurableSet_Icc.prod (measurableSet_le
          ((continuous_subtype_val.sub continuous_const).norm.measurable) measurable_const)
    · rw [indicator_of_notMem ht]
      have he : (fun p : ℝ×Sphere=>A.indicator (fun z=>g z.1) (t,p))=0 := by
        funext p
        simp [A,ht,indicator]
      change (∫⁻p : ℝ×Sphere,A.indicator (fun z=>g z.1) (t,p) ∂volume.prod sphereMeasure)=_
      rw [he]
      exact lintegral_zero
  calc
    _ ≤ ∫⁻z : ConeCoordinate,g z.1 ∂(volume.prod (volume.prod sphereMeasure)).restrict A :=
      lintegral_mono_set hsub
    _ = ∫⁻z : ConeCoordinate,A.indicator (fun z=>g z.1) z ∂volume.prod (volume.prod sphereMeasure) :=
      (lintegral_indicator hA _).symm
    _ = _ := hm
    _ ≤ ∫⁻t in J,g t*(ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by
      apply lintegral_mono
      intro t
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      convert sphere_cap_area (by positivity : 0≤4*φ) (velocity (V t)) using 1
      congr 1
      ring
    _ = _ := by
      rw [lintegral_mul_const _ hg]
      ac_rfl

lemma physicalBin_radial_density_near {s : Solution} {X V : ℝ→Vec}
    (hV : Measurable V) (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J)
    {C p θ φ : ℝ} (_hC : 0≤C) (_hp : 0≤p) (_hθ : 0≤θ) (hφ : 0≤φ)
    (hr : 0≤B.rmax) (hD : B.Dmax≤8*φ^2)
    (hdensity : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2≤ENNReal.ofReal (128*C*p^3*θ^2))
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)≤
      (∫⁻t in J,g t)*ENNReal.ofReal (49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin)) := by
  have hm := physicalBinMeasure_receiver_weight hV B hJ hφ hD hg
  have hbound : (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)≤
      (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)*
        (ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2)) := by
    calc
      _ ≤ ∫⁻z : ConeCoordinate,g z.1*(ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2))
          ∂physicalBinMeasure V B J := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
        have hr' : ENNReal.ofReal (z.1-z.2.1)≤ENNReal.ofReal B.rmax := ENNReal.ofReal_le_ofReal hz.2.2.1.2
        have hd := hdensity z hz
        simpa only [mul_assoc] using mul_le_mul' (mul_le_mul' le_rfl hr') hd
      _ = _ := lintegral_mul_const _ (hg.comp measurable_fst)
  by_cases hwidth : B.rmin≤B.rmax
  · calc
      _ ≤ (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)*
          (ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2)) := hbound
      _ ≤ (∫⁻t in J,g t)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)*
          (ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2)) := mul_le_mul' hm le_rfl
      _ = _ := by
        have he : 49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin)=
            (B.rmax-B.rmin)*(384*φ^2)*(B.rmax*(128*C*p^3*θ^2)) := by ring
        rw [he,ENNReal.ofReal_mul (by positivity : 0≤(B.rmax-B.rmin)*(384*φ^2)),
          ENNReal.ofReal_mul (sub_nonneg.mpr hwidth),ENNReal.ofReal_mul hr]
        ac_rfl
  · have hw : ENNReal.ofReal (B.rmax-B.rmin)=0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
    have hzero : (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)=0 := by
      apply le_antisymm
      · change (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)≤(0:ℝ≥0∞)
        simpa only [hw,mul_zero,zero_mul] using hm
      · exact bot_le
    calc
      _ ≤ (0:ℝ≥0∞) := by simpa only [hzero,zero_mul] using hbound
      _ ≤ _ := bot_le

end RVM

end

end OAI
