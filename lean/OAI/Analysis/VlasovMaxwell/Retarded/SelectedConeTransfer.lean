import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.PhysicalBinPhaseSet
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma selectedDyadicCutoff_active {ι : Type*} [Fintype ι] {Q : Set (ι→ℕ)} {x : ι→ℝ}
    (h : selectedDyadicCutoff Q x≠0) : ∃k∈Q,0<dyadicMultiFactor k x := by
  classical
  by_contra hh
  push Not at hh
  apply h
  suffices hz : ∀k, Q.indicator (fun k=>dyadicMultiFactor k x) k=0 by
    simp only [selectedDyadicCutoff,hz,tsum_zero]
  intro k
  by_cases hk : k∈Q
  · rw [Set.indicator_of_mem hk]
    exact le_antisymm (hh k hk) (dyadicMultiFactor_nonneg _ _)
  · exact Set.indicator_of_notMem hk _

lemma stateCutoff_physical_cover {T w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) {n : Sphere} {v : Vec}
    (Q : Set (Fin 4→ℕ)) (hd : stateCutoff T Q (t-σ,n.1,v,V t)≠0) :
    ∃k∈Q,((t,σ,n),v)∈physicalBinPhaseSet V (representativeClosedBin T w k) J := by
  obtain ⟨k,hk,hpos⟩ := selectedDyadicCutoff_active hd
  exact ⟨k,hk,physicalCutoff_positive_closedBin ht hσ hband hpos⟩

def selectedConeKernel (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (p : ConeKernelState) : Vec :=
  stateCutoff T Q (coneCutoffState α zX p) • A p

def selectedConeTriangle (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    (J : Set ℝ) (p : TrianglePhase) : Vec :=
  J.indicator W p.1.1 (triangleConeKernel s α zX T (selectedConeKernel α zX T Q A) p)

lemma PhaseFlowOn.selectedConeKernel_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T)) :
    ContinuousOn (selectedConeKernel F.flow zX T Q A) (coneKernelInterior T) := by
  have hcut : ContinuousOn (fun p=>stateCutoff T Q (coneCutoffState F.flow zX p))
      (coneKernelInterior T) := by
    intro p hp
    exact ((contDiffAt_stateCutoff T Q (sub_pos.mpr hp.2)
      (by simpa only [coneCutoffState,mem_sphere,dist_zero_right] using hp.1.2.1)).continuousAt).comp_continuousWithinAt
        (F.coneCutoffState_continuousOn zX p hp)
  exact hcut.smul hA

lemma labelConeKernel_selected (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (p : ℝ×Phase) :
    labelConeKernel s α zX T (selectedConeKernel α zX T Q A) p=
      labelSelectedCutoff α zX T Q p • labelConeKernel s α zX T A p := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · have hj : p∈jointBranchDomain α zX T := hp
    simp only [labelConeKernel,Set.indicator_of_mem hp,labelSelectedCutoff,Set.indicator_of_mem hj,
      selectedConeKernel,stateCutoff,coneCutoffState,labelKernelState,actualCutoffCoordinates]
    module
  · simp only [labelConeKernel,Set.indicator_of_notMem hp,smul_zero]

lemma selectedConeTriangle_eq_kernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec) (J : Set ℝ) :
    selectedConeTriangle s α zX T Q A W J=
      triangleConeKernel s α zX T (fun p=>J.indicator W p.1.1 (selectedConeKernel α zX T Q A p)) := by
  funext p
  exact (triangleConeKernel_receiver_multiplier s α zX T _ (J.indicator W) p).symm

lemma PhaseFlowOn.selectedConeTriangle_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable (selectedConeTriangle s F.flow zX T Q A W J) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp
    (((hW.indicator hJ).comp measurable_fst.fst).prodMk
      (F.triangleConeKernel_measurable_interior hs zX (F.selectedConeKernel_continuousOn zX Q hA)))

lemma PhaseFlowOn.selectedConeTriangle_norm_transfer {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      (labelSelectedCutoff F.flow zX T Q p • labelConeKernel s F.flow zX T A p)‖)=
      ∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q A W J p‖ ∂trianglePhaseMeasure := by
  classical
  have hm := F.selectedConeTriangle_measurable hs zX Q hA hW hJ
  rw [selectedConeTriangle_eq_kernel] at hm ⊢
  rw [F.triangleConeKernel_lintegral_norm_measurable zX hm]
  have ha := F.selectedConeKernel_continuousOn zX Q hA
  have hmA : Measurable ((coneKernelInterior T).indicator (selectedConeKernel F.flow zX T Q A)) :=
    ha.measurable_piecewise continuousOn_const (measurableSet_coneKernelInterior T)
  have he := F.labelConeKernel_triangle_norm_localBorel hs hT zX
    (localBorel_clm_apply hmA (hW.indicator hJ))
  simpa only [labelConeKernel_receiver_multiplier,labelConeKernel_selected] using he

lemma PhaseFlowOn.selectedConeTriangle_support {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (p : TrianglePhase) (hp : selectedConeTriangle s F.flow zX T Q A W J p≠0) :
    ∃k∈Q,p∈physicalBinPhaseSet (fun t=>(prefixFlow F.flow T zX t).2)
      (representativeClosedBin T w k) J := by
  classical
  have ht : p.1.1∈J := by
    by_contra hh
    exact hp (by simp only [selectedConeTriangle,Set.indicator_of_notMem hh,zero_apply])
  have hd : p∈trianglePhaseDomain T := by
    by_contra hh
    exact hp (by simp only [selectedConeTriangle,triangleConeKernel,Set.indicator_of_notMem hh,map_zero])
  have hc : stateCutoff T Q (p.1.1-p.1.2.1,p.1.2.2.1,p.2,(F.flow zX p.1.1).2)≠0 := by
    intro hh
    apply hp
    simp only [selectedConeTriangle,triangleConeKernel,Set.indicator_of_mem hd,selectedConeKernel,
      coneCutoffState,triangleKernelState,hh,zero_smul,smul_zero,map_zero]
  have hpre : (prefixFlow F.flow T zX p.1.1).2=(F.flow zX p.1.1).2 := by
    simp only [prefixFlow,prefixClamp_eq (hJT ht)]
  apply stateCutoff_physical_cover ht ⟨hd.2.1.le,hd.2.2.le⟩
    (V:=fun t=>(prefixFlow F.flow T zX t).2) (by rw [hpre]; exact hband _ ht) Q
  simpa only [hpre] using hc

lemma PhaseFlowOn.selectedConeTriangle_physical_sum {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (Q : Set (Fin 4→ℕ)) {A : ConeKernelState→Vec}
    (hA : ContinuousOn A (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec} (hW : Measurable W)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) :
    (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q A W J p‖ ∂trianglePhaseMeasure)≤
      ∑'k : Fin 4→ℕ,Q.indicator (fun k=>∫⁻z : ConeCoordinate,
        ∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
          ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T Q A W J (z,v)‖ ∂volume
            ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  apply physicalBinPhase_cover_lintegral hV hJ T w Q
    (F.selectedConeTriangle_measurable hs zX Q hA hW hJ).norm.ennreal_ofReal
  intro p hp
  apply F.selectedConeTriangle_support zX Q A W hJT hband p
  intro hh
  exact hp (by rw [hh,norm_zero,ENNReal.ofReal_zero])

end RVM

end

end OAI
