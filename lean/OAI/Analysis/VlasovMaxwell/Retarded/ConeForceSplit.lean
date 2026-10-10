import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.SelectedRemainderPhysical

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma selectedDyadicCutoff_compl {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hp : ∀i,0<x i) (h1 : ∀i,x i≤1) (Q : Set (ι→ℕ)) :
    selectedDyadicCutoff Qᶜ x=1-selectedDyadicCutoff Q x := by
  classical
  obtain ⟨N,hN,he⟩ := dyadicMultiFactor_curve_locally_finite
    (g:=fun i (_t : ℝ)=>x i) (t:=0) (fun _=>continuousAt_const) hp
  have hQ := (selectedDyadicCutoff_local_box he Q).eq_of_nhds
  have hQc := (selectedDyadicCutoff_local_box he Qᶜ).eq_of_nhds
  change selectedDyadicCutoff Q x=∑k∈selectedDyadicBox N Q,dyadicMultiFactor k x at hQ
  change selectedDyadicCutoff Qᶜ x=∑k∈selectedDyadicBox N Qᶜ,dyadicMultiFactor k x at hQc
  rw [hQ,hQc,selectedDyadicBox_compl]
  apply eq_sub_iff_add_eq.mpr
  have hs : selectedDyadicBox N Q ⊆ dyadicBox ι N := Finset.filter_subset _ _
  rw [Finset.sum_sdiff hs]
  exact sum_dyadicMultiFactor_eq_one N x h1 hN

lemma PhaseFlowOn.labelCutoff_compl_smul {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (A : ConeKernelState→Vec) (p : ℝ×Phase) :
    labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T A p=
      (1-labelSelectedCutoff F.flow zX T Q p) • labelConeKernel s F.flow zX T A p := by
  classical
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have ht := F.branch_time_mem zX p.2 hp.1 hp.2
    have hr : 0<branchTime F.flow zX p.2 T p.1-p.1 := sub_pos.mpr ht.1
    have hrT : branchTime F.flow zX p.2 T p.1-p.1≤ max 1 T := by
      have hσ := hp.1.1.1
      linarith only [ht.2,hσ,le_max_right (1:ℝ) T]
    have hn := F.branchDirection_norm zX p.2 hp.1 hp.2
    have hj : p∈jointBranchDomain F.flow zX T := hp
    simp only [labelSelectedCutoff,Set.indicator_of_mem hj,actualCutoffCoordinates]
    rw [selectedDyadicCutoff_compl (physicalCutoffCoordinates_pos hn hr)
      (physicalCutoffCoordinates_le_one hn hrT)]
  · simp only [labelConeKernel,Set.indicator_of_notMem hp,smul_zero]

def transportOnlyConeKernel (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : Vec :=
  normalisedSignedForce (p.1.1-p.1.2) (velocity (α zX p.1.1).2)
    (velocity p.2.2.2) p.2.1 0

def sourceOnlyConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : Vec :=
  sourceForceConeKernel s α zX p-transportOnlyConeKernel α zX p

lemma forceSourceKernel_zero (r : ℝ) (n a v : Vec) : forceSourceKernel r n a v 0=0 := by
  simp [forceSourceKernel,sourceNumerator,dot,receiverQ]

lemma normalised_transport_flux {r : ℝ} (n W v : Vec) (hr : r≠0) (hn : ‖n‖=1) :
    (1-dot n (velocity W)) • normalisedSignedForce r (velocity W) (velocity v) n 0=
      r^2 • forceTransportKernel r n (velocity W) v := by
  rw [normalisedSignedForce_flux _ _ _ _ hr hn (cone_denom_pos W n hn).ne',
    forceSourceKernel_zero,add_zero]

lemma normalised_source_flux {r : ℝ} (n W v b : Vec) (hr : r≠0) (hn : ‖n‖=1) :
    (1-dot n (velocity W)) •
      (normalisedSignedForce r (velocity W) (velocity v) n b-
       normalisedSignedForce r (velocity W) (velocity v) n 0)=
      r^2 • forceSourceKernel r n (velocity W) v b := by
  rw [smul_sub,normalisedSignedForce_flux _ _ _ _ hr hn (cone_denom_pos W n hn).ne',
    normalised_transport_flux n W v hr hn,smul_add,add_sub_cancel_left]

lemma PhaseFlowOn.transportOnlyConeKernel_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (transportOnlyConeKernel F.flow zX) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  refine continuousOn_normalisedSignedForce (continuous_fst.fst.sub continuous_fst.snd).continuousOn
    ha hu.continuousOn continuous_snd.fst.continuousOn continuousOn_const ?_ ?_
  · intro p hp
    exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  · intro p hp
    exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

lemma PhaseFlowOn.sourceOnlyConeKernel_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (sourceOnlyConeKernel s F.flow zX) (coneKernelDomain T) :=
  (F.normalised_source_force_continuousOn hs zX).sub (F.transportOnlyConeKernel_continuousOn zX)

lemma triangleConeKernel_add (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A B : ConeKernelState→Vec) (p : TrianglePhase) :
    triangleConeKernel s α zX T (fun q=>A q+B q) p=
      triangleConeKernel s α zX T A p+triangleConeKernel s α zX T B p := by
  classical
  by_cases hp : p∈trianglePhaseDomain T
  · simp only [triangleConeKernel,Set.indicator_of_mem hp,smul_add]
  · simp only [triangleConeKernel,Set.indicator_of_notMem hp,add_zero]

lemma labelConeKernel_add (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (A B : ConeKernelState→Vec) (p : ℝ×Phase) :
    labelConeKernel s α zX T (fun q=>A q+B q) p=
      labelConeKernel s α zX T A p+labelConeKernel s α zX T B p := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelConeKernel,Set.indicator_of_mem hp,smul_add]
  · simp only [labelConeKernel,Set.indicator_of_notMem hp,add_zero]

lemma triangleConeKernel_transport {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    {p : TrianglePhase} (hp : p∈trianglePhaseDomain T) :
    triangleConeKernel s α zX T (transportOnlyConeKernel α zX) p=
      (p.1.1-p.1.2.1)^2 • (s.f (p.1.2.1,((α zX p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)) •
        forceTransportKernel (p.1.1-p.1.2.1) p.1.2.2.1 (velocity (α zX p.1.1).2) p.2) := by
  simp only [triangleConeKernel,Set.indicator_of_mem hp,transportOnlyConeKernel,triangleKernelState]
  rw [smul_comm,normalised_transport_flux _ _ _ (sub_pos.mpr hp.2.2).ne' (sphere_norm _),smul_comm]

lemma triangleConeKernel_source {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    {p : TrianglePhase} (hp : p∈trianglePhaseDomain T) :
    triangleConeKernel s α zX T (sourceOnlyConeKernel s α zX) p=
      (p.1.1-p.1.2.1)^2 • (s.f (p.1.2.1,((α zX p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)) •
        forceSourceKernel (p.1.1-p.1.2.1) p.1.2.2.1 (velocity (α zX p.1.1).2) p.2
          (sourceAcceleration s (p.1.2.1,((α zX p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) := by
  simp only [triangleConeKernel,Set.indicator_of_mem hp,sourceOnlyConeKernel,sourceForceConeKernel,
    transportOnlyConeKernel,triangleKernelState]
  rw [smul_comm,normalised_source_flux _ _ _ _ (sub_pos.mpr hp.2.2).ne' (sphere_norm _),smul_comm]

lemma PhaseFlowOn.unselected_force_norm_split {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (W : ℝ→Vec→L[ℝ]Vec) (J : Set ℝ) (p : ℝ×Phase) :
    ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p)‖≤
      ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
        (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (transportOnlyConeKernel F.flow zX) p)‖+
      ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
        (labelSelectedCutoff F.flow zX T Qᶜ p • labelConeKernel s F.flow zX T (sourceOnlyConeKernel s F.flow zX) p)‖ := by
  rw [F.actualLabelSignedForce_eq_normalised zX,←F.labelCutoff_compl_smul zX Q]
  have he : sourceForceConeKernel s F.flow zX=
      fun q=>transportOnlyConeKernel F.flow zX q+sourceOnlyConeKernel s F.flow zX q := by
    funext q
    dsimp only [sourceOnlyConeKernel]
    abel
  rw [he,labelConeKernel_add,smul_add,map_add,←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.selectedTransportTriangle_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (p : TrianglePhase) :
    ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (transportOnlyConeKernel F.flow zX)
      (prefixAngularMultiplier s F.flow T w hw zX) J p‖≤
    ENNReal.ofReal 64*directTriangleDensity s (fun t=>(prefixFlow F.flow T zX t).1) T J
      (directTransportTriangleKernel (fun t=>(prefixFlow F.flow T zX t).2)) p := by
  classical
  apply (ENNReal.ofReal_le_ofReal (selectedConeTriangle_norm_le Q _ _ J p)).trans
  by_cases ht : p.1.1∈J
  · rw [Set.indicator_of_mem ht]
    by_cases hp : p∈trianglePhaseDomain T
    · have htime := hJT ht
      have hσ : p.1.2.1∈Icc 0 T := ⟨hp.2.1.le, hp.2.2.le.trans htime.2⟩
      rw [(prefixAngular_highband hw zX htime (hband _ ht)).1,triangleConeKernel_transport hp]
      have hbound : ‖angularMultiplierCLM w (F.flow zX p.1.1).2‖≤64 :=
        angularMultiplierCLM_norm_le hw (by linarith only [hband _ ht,hw])
      have hnorm := (angularMultiplierCLM w (F.flow zX p.1.1).2).le_opNorm
        ((p.1.1-p.1.2.1)^2 • (s.f (p.1.2.1,((F.flow zX p.1.1).1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)) •
          forceTransportKernel (p.1.1-p.1.2.1) p.1.2.2.1 (velocity (F.flow zX p.1.1).2) p.2))
      have hn := hnorm.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
      apply (ENNReal.ofReal_le_ofReal hn).trans_eq
      simp only [directTriangleDensity,Set.indicator_of_mem (show p∈directTriangleDomain T J from ⟨hp,ht⟩),
        prefixParticle,prefixFlow,prefixClamp_eq htime,prefixClamp_eq hσ,directTransportTriangleKernel,
        norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (p.1.1-p.1.2.1))]
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤64),ENNReal.ofReal_mul (sq_nonneg _)]
    · simp only [triangleConeKernel,Set.indicator_of_notMem hp,map_zero,norm_zero,ENNReal.ofReal_zero]
      exact bot_le
  · simp only [Set.indicator_of_notMem ht,zero_apply,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma PhaseFlowOn.selectedSourceTriangle_density_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hw : 0<w) (zX : Phase) (Q R : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      physicalProjectedSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B T w R z := by
  classical
  unfold physicalProjectedSourceDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  apply (ENNReal.ofReal_le_ofReal (selectedConeTriangle_norm_le Q _ _ J (z,v))).trans
  rw [Set.indicator_of_mem hz.1]
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have ht := hJT hz.1
    rw [(prefixAngular_highband hw zX ht (hband _ hz.1)).1,triangleConeKernel_source hp,map_smul]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (z.1-z.2.1)),
      ENNReal.ofReal_mul (sq_nonneg (z.1-z.2.1))]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    simp only [prefixFlow,prefixClamp_eq ht,sourceAcceleration,map_smul,norm_smul,Real.norm_eq_abs]
    exact le_add_of_nonneg_right (by positivity)
  · simp only [triangleConeKernel,Set.indicator_of_notMem hp,map_zero,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma PhaseFlowOn.selectedSourceTriangle_majorant_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q (sourceOnlyConeKernel s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      ENNReal.ofReal 64*physicalSourceMajorantDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B z := by
  classical
  unfold physicalSourceMajorantDensity
  rw [←mul_assoc,←lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro v
  apply (ENNReal.ofReal_le_ofReal (selectedConeTriangle_norm_le Q _ _ J (z,v))).trans
  rw [Set.indicator_of_mem hz.1]
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have ht := hJT hz.1
    have hσ : z.2.1∈Icc 0 T := ⟨hp.2.1.le,hp.2.2.le.trans ht.2⟩
    have hf := hs.nonnegative z.2.1 hσ ((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)
    rw [(prefixAngular_highband hw zX ht (hband _ hz.1)).1,triangleConeKernel_source hp]
    have hbound : ‖angularMultiplierCLM w (F.flow zX z.1).2‖≤64 :=
      angularMultiplierCLM_norm_le hw (by linarith only [hband _ hz.1,hw])
    have hn := (angularMultiplierCLM w (F.flow zX z.1).2).le_opNorm
      ((z.1-z.2.1)^2 • (s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)) •
        forceSourceKernel (z.1-z.2.1) z.2.2.1 (velocity (F.flow zX z.1).2) v
          (sourceAcceleration s (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)))))
    apply (ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _)))).trans
    simp only [prefixFlow,prefixClamp_eq ht]
    rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤64),←ENNReal.ofReal_mul (by positivity : (0:ℝ)≤64*(z.1-z.2.1)^2)]
    apply ENNReal.ofReal_le_ofReal
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (z.1-z.2.1)),abs_of_nonneg hf]
    have hh := forceSourceKernel_le_majorant z.2.2.1 (F.flow zX z.1).2 v
      (s.E (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1))
      (s.B (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)) (sub_pos.mpr hp.2.2) (sphere_norm _)
    dsimp only [sourceAcceleration,lorentzField,lorentzPhase] at ⊢
    nlinarith only [mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg (z.1-z.2.1)) hf)]
  · simp only [triangleConeKernel,Set.indicator_of_notMem hp,map_zero,norm_zero,ENNReal.ofReal_zero]
    exact bot_le

end RVM

end

end OAI
