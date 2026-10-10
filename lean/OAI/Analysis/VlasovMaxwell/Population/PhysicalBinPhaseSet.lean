import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.SelectedReceiverWeightBoundFinite
import OAI.Analysis.VlasovMaxwell.Retarded.PhysicalProjectedRemainderDensity
import OAI.Analysis.VlasovMaxwell.Regularity.NormalisedPartialCutoff

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

lemma measurableSet_coneMomentumFiber {V : ℝ→Vec} (hV : Measurable V) (B : ClosedConeBin) :
    MeasurableSet {p : ConeCoordinate×Vec | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))} := by
  have hn : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate×Vec=>velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate×Vec=>velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst.fst)
  exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
    ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
      (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))

def physicalBinPhaseSet (V : ℝ→Vec) (B : ClosedConeBin) (J : Set ℝ) : Set TrianglePhase :=
  {p | p.1∈physicalBinBase V B J ∧ p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))}

lemma measurableSet_physicalBinPhaseSet {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (physicalBinPhaseSet V B J) :=
  ((measurableSet_physicalBinBase hV B hJ).preimage measurable_fst).inter
    (measurableSet_coneMomentumFiber hV B)

lemma physicalBinPhase_integral {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J)
    {g : TrianglePhase→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻p in physicalBinPhaseSet V B J,g p ∂trianglePhaseMeasure)=
      ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        g (z,v) ∂volume ∂physicalBinMeasure V B J := by
  classical
  rw [←lintegral_indicator (measurableSet_physicalBinPhaseSet hV B hJ)]
  rw [trianglePhaseMeasure,lintegral_prod _ (hg.indicator (measurableSet_physicalBinPhaseSet hV B hJ)).aemeasurable]
  rw [physicalBinMeasure,←lintegral_indicator (measurableSet_physicalBinBase hV B hJ)]
  apply lintegral_congr
  intro z
  by_cases hz : z∈physicalBinBase V B J
  · rw [indicator_of_mem hz,←lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
    apply lintegral_congr
    intro v
    by_cases hv : v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1))
    · rw [indicator_of_mem (show (z,v)∈physicalBinPhaseSet V B J from ⟨hz,hv⟩),indicator_of_mem hv]
    · rw [indicator_of_notMem (show (z,v)∉physicalBinPhaseSet V B J from fun h=>hv h.2),indicator_of_notMem hv]
  · rw [indicator_of_notMem hz]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun v=>indicator_of_notMem (show (z,v)∉physicalBinPhaseSet V B J from fun h=>hz h.1) _)

lemma stateCutoff_derivative_physical_cover {T w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (htT : t≤T) (hσ : σ∈Ico 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) {n : Sphere} {v : Vec} {N : ℕ}
    (hP : 1024*q v≤(2:ℝ)^N) (Q : Set (Fin 4→ℕ)) (H : CutoffState)
    (hd : fderiv ℝ (stateCutoff T Q) (t-σ,n.1,v,V t) H≠0) :
    ∃k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N},
      ((t,σ,n),v)∈physicalBinPhaseSet V (representativeClosedBin T w k) J := by
  have hr : 0<t-σ := sub_pos.mpr hσ.2
  have hrT : t-σ ≤ max 1 T := by linarith [hσ.1,le_max_right (1:ℝ) T]
  obtain ⟨j,hj,k,hk,hjp,hkp,_⟩ := stateCutoff_partial_boundary (z:=(t-σ,n.1,v,V t)) Q hr hrT (sphere_norm n) H hd
  have hnear := dyadicMultiFactor_positive_index_comparison hjp hkp
  have hjb : j∈dyadicSelectionBoundary Q :=
    ⟨⟨j,hj,fun i=>⟨Nat.le_add_right (j i) 2,Nat.le_add_right (j i) 2⟩⟩,⟨k,hk,fun i=>hnear i⟩⟩
  exact ⟨j,⟨hjb,physicalCutoff_positive_source_indices (sphere_norm n) hP hjp⟩,
    physicalCutoff_positive_closedBin ht ⟨hσ.1,hσ.2.le⟩ hband hjp⟩

lemma physicalBinPhase_cover_lintegral {V : ℝ→Vec} (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (T w : ℝ) (R : Set (Fin 4→ℕ))
    {g : TrianglePhase→ℝ≥0∞} (hg : Measurable g)
    (hcover : ∀p,g p≠0→∃k∈R,p∈physicalBinPhaseSet V (representativeClosedBin T w k) J) :
    (∫⁻p,g p ∂trianglePhaseMeasure)≤
      ∑'k : Fin 4→ℕ,R.indicator (fun k=>
        ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k)
          z.2.2.1 (velocity (V z.1)),g (z,v) ∂volume
          ∂physicalBinMeasure V (representativeClosedBin T w k) J) k := by
  classical
  let f : (Fin 4→ℕ)→TrianglePhase→ℝ≥0∞ := fun k=>
    if k∈R then (physicalBinPhaseSet V (representativeClosedBin T w k) J).indicator g else 0
  have hm (k : Fin 4→ℕ) : Measurable (f k) := by
    dsimp only [f]
    split_ifs
    · exact hg.indicator (measurableSet_physicalBinPhaseSet hV _ hJ)
    · exact measurable_const
  calc
    _ ≤ ∫⁻p,∑'k : Fin 4→ℕ,f k p ∂trianglePhaseMeasure := by
      apply lintegral_mono
      intro p
      by_cases hp : g p=0
      · rw [hp]; exact bot_le
      · obtain ⟨k,hk,hpk⟩ := hcover p hp
        calc
          _ = f k p := by simp only [f,ite_eq_left hk,indicator_of_mem hpk]
          _ ≤ _ := ENNReal.le_tsum (f := fun index => f index p) k
    _ = ∑'k : Fin 4→ℕ,∫⁻p,f k p ∂trianglePhaseMeasure := lintegral_tsum (fun k=>(hm k).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro k
      by_cases hk : k∈R
      · simp only [f,ite_eq_left hk,indicator_of_mem hk]
        rw [lintegral_indicator (measurableSet_physicalBinPhaseSet hV _ hJ),physicalBinPhase_integral hV _ hJ hg]
      · simp only [f,ite_eq_right hk,Pi.zero_apply,lintegral_zero,indicator_of_notMem hk]

lemma PhaseFlowOn.triangleConeKernel_measurable_interior {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelInterior T)) :
    Measurable (triangleConeKernel s F.flow zX T A) := by
  classical
  have hS := F.triangleKernelState_continuousOn zX
  have hSA := hA.comp hS (fun _ hp=>⟨triangleKernelState_mem _ _ hp,hp.2.2⟩)
  have hSf := hs.f_smooth.continuousOn.comp (hS.fst.snd.prodMk hS.snd.snd)
    (fun _ hp=>⟨(triangleKernelState_mem F.flow zX hp).1.2,mem_univ _⟩)
  have hV : ContinuousOn (fun p : TrianglePhase=>(F.flow zX p.1.1).2) (trianglePhaseDomain T) :=
    ((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn
      (fun _ hp=>Ioo_subset_Icc_self hp.1)).snd
  have hD : ContinuousOn (fun p : TrianglePhase=>1-dot p.1.2.2.1 (velocity (F.flow zX p.1.1).2))
      (trianglePhaseDomain T) := by
    simp only [dot_eq_inner]
    exact continuousOn_const.sub (continuous_fst.snd.snd.subtype_val.continuousOn.inner
      ((contDiff_velocity (k:=1)).continuous.comp_continuousOn hV))
  exact (hD.smul (hSf.smul hSA)).measurable_piecewise continuousOn_const
    (measurableSet_trianglePhaseDomain T)

def partialCutoffTriangle (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) (H : ConeKernelState→CutoffState)
    (W : ℝ→Vec→L[ℝ]Vec) (J : Set ℝ) : TrianglePhase→Vec :=
  {p : TrianglePhase | p.1.1∈J}.indicator (fun p=>W p.1.1
    (triangleConeKernel s α zX T (normalisedPartialCutoff α zX T Q H) p))

lemma partialCutoffTriangle_of_mem {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    {Q : Set (Fin 4→ℕ)} {H : ConeKernelState→CutoffState} {W : ℝ→Vec→L[ℝ]Vec}
    {J : Set ℝ} {p : TrianglePhase} (ht : p.1.1∈J) :
    partialCutoffTriangle s α zX T Q H W J p =
      W p.1.1 (triangleConeKernel s α zX T (normalisedPartialCutoff α zX T Q H) p) :=
  indicator_of_mem (show p∈{p : TrianglePhase | p.1.1∈J} from ht) _

lemma partialCutoffTriangle_of_notMem {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    {Q : Set (Fin 4→ℕ)} {H : ConeKernelState→CutoffState} {W : ℝ→Vec→L[ℝ]Vec}
    {J : Set ℝ} {p : TrianglePhase} (ht : p.1.1∉J) :
    partialCutoffTriangle s α zX T Q H W J p = 0 :=
  indicator_of_notMem (show p∉{p : TrianglePhase | p.1.1∈J} from ht) _

lemma PhaseFlowOn.partialCutoffTriangle_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    Measurable (partialCutoffTriangle s F.flow zX T Q H W J) := by
  apply Measurable.indicator _ (hJ.preimage measurable_fst.fst)
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp
    ((hW.comp measurable_fst.fst).prodMk (F.triangleConeKernel_measurable_interior hs zX
      (F.normalisedPartialCutoff_continuousOn zX Q hH)))

lemma PhaseFlowOn.partialCutoffTriangle_support {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    (H : ConeKernelState→CutoffState) (W : ℝ→Vec→L[ℝ]Vec)
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N)
    {p : TrianglePhase} (hp : partialCutoffTriangle s F.flow zX T Q H W J p≠0) :
    ∃k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N},
      p∈physicalBinPhaseSet (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J := by
  classical
  have ht : p.1.1∈J := by
    by_contra hc
    exact hp (partialCutoffTriangle_of_notMem hc)
  have hc : p∈trianglePhaseDomain T := by
    by_contra hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_notMem hh,map_zero]
  have hf : s.f ((triangleKernelState F.flow zX p).1.2,(triangleKernelState F.flow zX p).2.2)≠0 := by
    intro hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_mem hc,hh,
      zero_smul,smul_zero,map_zero]
  have hd : fderiv ℝ (stateCutoff T Q) (coneCutoffState F.flow zX (triangleKernelState F.flow zX p))
      (H (triangleKernelState F.flow zX p))≠0 := by
    intro hh
    apply hp
    simp only [partialCutoffTriangle_of_mem ht,triangleConeKernel,indicator_of_mem hc,
      normalisedPartialCutoff,hh,zero_smul,smul_zero,map_zero]
  have he : (prefixFlow F.flow T zX p.1.1).2=(F.flow zX p.1.1).2 := by
    simp only [prefixFlow,prefixClamp_eq (hJT ht)]
  have hdp : fderiv ℝ (stateCutoff T Q)
      (p.1.1-p.1.2.1,p.1.2.2.1,p.2,(prefixFlow F.flow T zX p.1.1).2)
      (H (triangleKernelState F.flow zX p))≠0 := by
    rw [he]
    exact hd
  exact stateCutoff_derivative_physical_cover ht (hJT ht).2 ⟨hc.2.1.le,hc.2.2⟩
    (by rw [he]; exact hband _ ht)
    (hP _ ⟨hc.2.1.le,hc.2.2.le.trans hc.1.2.le⟩ _ hf) Q _ hdp

lemma PhaseFlowOn.partialCutoffTriangle_boundary_sum {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) :
    (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J p‖ ∂trianglePhaseMeasure)≤
      ∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator (fun k=>
        ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (representativeClosedBin T w k)
          z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
          ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J (z,v)‖ ∂volume
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
  apply physicalBinPhase_cover_lintegral hV hJ T w _
    (F.partialCutoffTriangle_measurable hs zX Q hH hW hJ).norm.ennreal_ofReal
  intro p hp
  apply F.partialCutoffTriangle_support zX Q H W hJT hband N hP
  intro hh
  exact hp (by rw [hh,norm_zero,ENNReal.ofReal_zero])

lemma normalised_partial_kernel_eq {r f D l : ℝ} {a u n : Vec}
    (hr : r≠0) (hd : 1-dot n u≠0) (W : Vec→L[ℝ]Vec) :
    W (D • (f • (l • normalisedPrimitive r a u n)))=
      r^2 • ((f*D/(r*(1-dot n u))*l) • W (signedPrimitive a u n)) := by
  simp only [normalisedPrimitive,map_smul,smul_smul]
  congr 1
  field_simp

def coneReceiverCutoffTangent (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : CutoffState :=
  (0,0,0,(coneCutoffRate s α zX p).2.2.2)

lemma PhaseFlowOn.coneReceiverCutoffTangent_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneReceiverCutoffTangent s F.flow zX) (coneKernelInterior T) :=
  continuousOn_const.prodMk (continuousOn_const.prodMk (continuousOn_const.prodMk
    (F.coneCutoffRate_continuousOn hs zX).snd.snd.snd))

lemma PhaseFlowOn.partialCutoffTriangle_receiver_density_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q (coneReceiverCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      physicalReceiverCutoffDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B T w Q (prefixMomentumForce s F.flow T zX) z := by
  classical
  unfold physicalReceiverCutoffDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  dsimp only
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have htime := hJT hz.1
    have hprefix : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq htime]
    have hK : prefixMomentumForce s F.flow T zX z.1=
        (lorentzField s.E s.B (z.1,F.flow zX z.1)).2 := by
      simp only [prefixMomentumForce,hprefix,prefixClamp_eq htime]
    have he := normalised_partial_kernel_eq (sub_pos.mpr hp.2.2).ne'
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).ne'
      (angularMultiplierCLM w (F.flow zX z.1).2)
      (f:=s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)))
      (D:=1-dot z.2.2.1 (velocity (F.flow zX z.1).2))
      (l:=fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
        (cutoffReceiverTangent ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (F.flow zX z.1).2)))
          (lorentzField s.E s.B (z.1,F.flow zX z.1)).2))
      (a:=velocity (F.flow zX z.1).2)
    have htriangle : partialCutoffTriangle s F.flow zX T Q (coneReceiverCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)=
      (z.1-z.2.1)^2 • ((s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (F.flow zX z.1).2))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
          fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
            (cutoffReceiverTangent ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (F.flow zX z.1).2)))
              (lorentzField s.E s.B (z.1,F.flow zX z.1)).2)) •
        angularMultiplierCLM w (F.flow zX z.1).2 (signedPrimitive (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1)) := by
      simpa only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_mem hp,
        (prefixAngular_highband hw zX htime (hband _ hz.1)).1,normalisedPartialCutoff,
        coneReceiverCutoffTangent,coneCutoffRate,coneCutoffState,triangleKernelState,cutoffReceiverTangent] using he
    rw [htriangle,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),ENNReal.ofReal_mul (sq_nonneg _),hprefix,hK]
  · simp only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_notMem hp,map_zero,
      norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma Admissible.actual_receiverCutoff_triangle_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) → 0≤T →
      ∀(zX : Phase) (J : Set ℝ) (w κ : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)) (hw : 0<w),
      MeasurableSet J → J⊆Icc 0 T → 0≤κ → κ≤1/64 →
      (∀j∈Q,cappedRepresentative (j 1)≤κ*cappedRepresentative (j 2) ∧
        sourceRepresentative (j 0)*cappedRepresentative (j 1)*
          Real.sqrt (max 1 T*cappedRepresentative (j 3))≤1) →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) →
      (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
        (coneReceiverCutoffTangent s F.flow zX) (prefixAngularMultiplier s F.flow T w hw zX) J p‖
        ∂trianglePhaseMeasure)≤
      (∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.receiver_cutoff_boundary_sum
  refine ⟨C,hC,?_⟩
  intro s T F hs h0 hT zX J w κ N Q hw hJ hJT hκ hκsmall hQ hq hband hP
  let X : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).1
  let V : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  have hα : Continuous (prefixFlow F.flow T zX) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hV : Measurable V := hα.snd.measurable
  have hK : Measurable K := (F.continuous_prefixMomentumForce hs hT zX).measurable
  have hW := (F.prefixAngular_regular hs hT hw zX).1.measurable
  have hmain := F.partialCutoffTriangle_boundary_sum hs hT zX Q
    (F.coneReceiverCutoffTangent_continuousOn hs zX) hW hJ hJT hq N hP
  apply hmain.trans
  apply le_trans _ (hbound s T F hs h0 X V K J w κ N Q hV hK hJ hJT hw hκ hκsmall hQ (fun t ht=>by
    simpa only [V,prefixFlow,prefixClamp_eq (hJT ht)] using hband t ht))
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}
  · simp only [indicator_of_mem hk]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV (representativeClosedBin T w k) hJ)] with z hz
    exact F.partialCutoffTriangle_receiver_density_le hw zX Q hJT hband _ hz
  · simp only [indicator_of_notMem hk]
    exact le_rfl

lemma PhaseFlowOn.triangleConeKernel_lintegral_norm_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {A : ConeKernelState→Vec} (hK : Measurable (triangleConeKernel s F.flow zX T A)) :
    (∫⁻p,ENNReal.ofReal ‖triangleConeKernel s F.flow zX T A p‖ ∂trianglePhaseMeasure)=
      ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (1-dot n.1 (velocity (F.flow zX t).2))*
        ∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v)))‖ ∂volume ∂sphereMeasure := by
  classical
  let g : TrianglePhase→ℝ≥0∞ := fun p=>ENNReal.ofReal ‖triangleConeKernel s F.flow zX T A p‖
  have hg : Measurable g := hK.norm.ennreal_ofReal
  have hm : Measurable (fun z : ConeCoordinate=>∫⁻v : Vec,g (z,v)) := hg.lintegral_prod_right'
  have he : (∫⁻p,g p ∂trianglePhaseMeasure)=
      ∫⁻t : ℝ,∫⁻σ : ℝ,∫⁻n : Sphere,∫⁻v : Vec,g ((t,σ,n),v) ∂volume ∂sphereMeasure := by
    rw [trianglePhaseMeasure,lintegral_prod _ hg.aemeasurable,lintegral_prod _ hm.aemeasurable]
    apply lintegral_congr
    intro t
    exact lintegral_prod _ ((hm.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  rw [he]
  rw [←lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  by_cases ht : t∈Ioo 0 T
  · rw [indicator_of_mem ht,←lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro σ
    by_cases hσ : σ∈Ioo 0 t
    · rw [indicator_of_mem hσ]
      apply lintegral_congr
      intro n
      rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro v
      have hp : ((t,σ,n),v)∈trianglePhaseDomain T := ⟨ht,hσ⟩
      simp only [g,triangleConeKernel,indicator_of_mem hp,triangleKernelState,
        norm_smul,Real.norm_eq_abs,abs_of_pos (cone_denom_pos _ _ (sphere_norm n)),
        ENNReal.ofReal_mul (cone_denom_pos _ _ (sphere_norm n)).le]
    · rw [indicator_of_notMem hσ]
      have hz : ∀n : Sphere,∀v : Vec,g ((t,σ,n),v)=0 := by
        intro n v
        have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>hσ hp.2
        simp only [g,triangleConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero]
      simp only [hz,lintegral_zero]
  · rw [indicator_of_notMem ht]
    have hz : ∀σ : ℝ,∀n : Sphere,∀v : Vec,g ((t,σ,n),v)=0 := by
      intro σ n v
      have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>ht hp.1
      simp only [g,triangleConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero]
    simp only [hz,lintegral_zero]

lemma partialCutoffTriangle_eq_kernel (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (Q : Set (Fin 4→ℕ)) (H : ConeKernelState→CutoffState)
    (W : ℝ→Vec→L[ℝ]Vec) (J : Set ℝ) :
    partialCutoffTriangle s α zX T Q H W J =
      triangleConeKernel s α zX T (fun p=>J.indicator W p.1.1 (normalisedPartialCutoff α zX T Q H p)) := by
  classical
  funext p
  rw [triangleConeKernel_receiver_multiplier]
  by_cases ht : p.1.1∈J
  · rw [partialCutoffTriangle_of_mem ht,indicator_of_mem ht]
  · rw [partialCutoffTriangle_of_notMem ht,indicator_of_notMem ht]
    rfl

lemma PhaseFlowOn.partialCutoffLabelCost_triangle {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {H : ConeKernelState→CutoffState}
    (hH : ContinuousOn H (coneKernelInterior T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : Measurable W) {J : Set ℝ} (hJ : MeasurableSet J) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator W (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q (H ∘ labelKernelState F.flow zX T) p)‖)=
      ∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q H W J p‖ ∂trianglePhaseMeasure := by
  have hm := F.partialCutoffTriangle_measurable hs zX Q hH hW hJ
  rw [partialCutoffTriangle_eq_kernel] at hm ⊢
  rw [F.triangleConeKernel_lintegral_norm_measurable zX hm,
    F.partialCutoffLabelCost_multiplier_polar hs hT zX Q hH (hW.indicator hJ)]
  simp only [map_smul]

lemma coneReceiverCutoffTangent_pullback (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) :
    coneReceiverCutoffTangent s α zX ∘ labelKernelState α zX T =
      fun p=>cutoffReceiverTangent (branchRate α zX p.2 T p.1)
        (lorentzField s.E s.B (branchTime α zX p.2 T p.1,α zX (branchTime α zX p.2 T p.1))).2 := by
  rfl

lemma Admissible.actual_receiverCutoff_label_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) → 0≤T →
      ∀(zX : Phase) (J : Set ℝ) (w κ : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)) (hw : 0<w),
      MeasurableSet J → J⊆Icc 0 T → 0≤κ → κ≤1/64 →
      (∀j∈Q,cappedRepresentative (j 1)≤κ*cappedRepresentative (j 2) ∧
        sourceRepresentative (j 0)*cappedRepresentative (j 1)*
          Real.sqrt (max 1 T*cappedRepresentative (j 3))≤1) →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T Q
          (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
            (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖)≤
      (∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.actual_receiverCutoff_triangle_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs h0 hT zX J w κ N Q hw hJ hJT hκ hκsmall hQ hq hband hP
  have he := F.partialCutoffLabelCost_triangle hs hT zX Q
    (F.coneReceiverCutoffTangent_continuousOn hs zX)
    (F.prefixAngular_regular hs hT hw zX).1.measurable hJ
  rw [coneReceiverCutoffTangent_pullback] at he
  rw [he]
  exact hbound s T F hs h0 hT zX J w κ N Q hw hJ hJT hκ hκsmall hQ hq hband hP

def coneSourceCutoffTangent (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : CutoffState :=
  (0,0,(coneCutoffRate s α zX p).2.2.1,0)

def coneGeometryCutoffTangent (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : CutoffState :=
  ((coneCutoffRate s α zX p).1,(coneCutoffRate s α zX p).2.1,0,0)

lemma PhaseFlowOn.coneSourceCutoffTangent_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneSourceCutoffTangent s F.flow zX) (coneKernelInterior T) :=
  continuousOn_const.prodMk (continuousOn_const.prodMk
    ((F.coneCutoffRate_continuousOn hs zX).snd.snd.fst.prodMk continuousOn_const))

lemma PhaseFlowOn.coneGeometryCutoffTangent_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneGeometryCutoffTangent s F.flow zX) (coneKernelInterior T) :=
  (F.coneCutoffRate_continuousOn hs zX).fst.prodMk
    ((F.coneCutoffRate_continuousOn hs zX).snd.fst.prodMk
      (continuousOn_const.prodMk continuousOn_const))

lemma coneSourceCutoffTangent_pullback (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) :
    coneSourceCutoffTangent s α zX ∘ labelKernelState α zX T =
      fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,α p.2 p.1)).2 := rfl

lemma coneGeometryCutoffTangent_pullback (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) :
    coneGeometryCutoffTangent s α zX ∘ labelKernelState α zX T =
      fun p=>cutoffGeometryTangent (branchTime α zX p.2 T p.1-p.1) (branchRate α zX p.2 T p.1)
        (velocity (α zX (branchTime α zX p.2 T p.1)).2) (velocity (α p.2 p.1).2)
        (branchDirection α zX p.2 T p.1) := rfl

lemma PhaseFlowOn.partialCutoffTriangle_source_density_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q (coneSourceCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      physicalProjectedSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B T w Q z := by
  classical
  unfold physicalProjectedSourceDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  dsimp only
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have htime := hJT hz.1
    have hprefix : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq htime]
    have he := normalised_partial_kernel_eq (sub_pos.mpr hp.2.2).ne'
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).ne'
      (angularMultiplierCLM w (F.flow zX z.1).2)
      (f:=s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)))
      (D:=1-dot z.2.2.1 (velocity (F.flow zX z.1).2))
      (l:=fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
        (cutoffSourceTangent
          (s.E (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)+
            cross (velocity v) (s.B (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)))))
      (a:=velocity (F.flow zX z.1).2)
    have htriangle : partialCutoffTriangle s F.flow zX T Q (coneSourceCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)=
      (z.1-z.2.1)^2 • ((s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (F.flow zX z.1).2))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
          fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
            (cutoffSourceTangent
              (s.E (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)+
                cross (velocity v) (s.B (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1))))) •
        angularMultiplierCLM w (F.flow zX z.1).2 (signedPrimitive (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1)) := by
      simpa only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_mem hp,
        (prefixAngular_highband hw zX htime (hband _ hz.1)).1,normalisedPartialCutoff,
        coneSourceCutoffTangent,coneCutoffRate,coneCutoffState,triangleKernelState,cutoffSourceTangent,lorentzField,lorentzPhase] using he
    rw [htriangle,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),ENNReal.ofReal_mul (sq_nonneg _),hprefix]
    apply mul_le_mul' le_rfl
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (norm_nonneg _))
  · simp only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_notMem hp,map_zero,
      norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma PhaseFlowOn.partialCutoffTriangle_geometry_density_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q (coneGeometryCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      physicalGeometryCutoffDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B T w Q z := by
  classical
  unfold physicalGeometryCutoffDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  dsimp only
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have htime := hJT hz.1
    have hprefix : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq htime]
    have he := normalised_partial_kernel_eq (sub_pos.mpr hp.2.2).ne'
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).ne'
      (angularMultiplierCLM w (F.flow zX z.1).2)
      (f:=s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)))
      (D:=1-dot z.2.2.1 (velocity (F.flow zX z.1).2))
      (l:=fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
        (cutoffGeometryTangent (z.1-z.2.1)
          ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (F.flow zX z.1).2)))
          (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1))
      (a:=velocity (F.flow zX z.1).2)
    have htriangle : partialCutoffTriangle s F.flow zX T Q (coneGeometryCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)=
      (z.1-z.2.1)^2 • ((s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (F.flow zX z.1).2))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
          fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
            (cutoffGeometryTangent (z.1-z.2.1)
              ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (F.flow zX z.1).2)))
              (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1)) •
        angularMultiplierCLM w (F.flow zX z.1).2 (signedPrimitive (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1)) := by
      simpa only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_mem hp,
        (prefixAngular_highband hw zX htime (hband _ hz.1)).1,normalisedPartialCutoff,
        coneGeometryCutoffTangent,coneCutoffRate,coneCutoffState,triangleKernelState,cutoffGeometryTangent] using he
    rw [htriangle,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),ENNReal.ofReal_mul (sq_nonneg _),hprefix]
  · simp only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_notMem hp,map_zero,
      norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma PhaseFlowOn.actual_sourceCutoff_label_boundary_sum {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (Q : Set (Fin 4→ℕ)) (hw : 0<w)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hq : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
      (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)≤
      ∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator (fun k=>
        ∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s
          (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
          (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  classical
  have hW := (F.prefixAngular_regular hs hT hw zX).1.measurable
  have hH := F.coneSourceCutoffTangent_continuousOn hs zX
  have he := F.partialCutoffLabelCost_triangle hs hT zX Q hH hW hJ
  rw [coneSourceCutoffTangent_pullback] at he
  rw [he]
  apply (F.partialCutoffTriangle_boundary_sum hs hT zX Q hH hW hJ hJT hq N hP).trans
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}
  · simp only [indicator_of_mem hk]
    apply lintegral_mono_ae
    have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
      ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV (representativeClosedBin T w k) hJ)] with z hz
    exact F.partialCutoffTriangle_source_density_le hw zX Q hJT hband _ hz
  · simp only [indicator_of_notMem hk]
    exact le_rfl

lemma PhaseFlowOn.actual_geometryCutoff_label_boundary_sum {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (Q : Set (Fin 4→ℕ)) (hw : 0<w)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hq : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
      (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q (fun p=>cutoffGeometryTangent (branchTime F.flow zX p.2 T p.1-p.1) (branchRate F.flow zX p.2 T p.1)
            (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2) (velocity (F.flow p.2 p.1).2)
            (branchDirection F.flow zX p.2 T p.1)) p)‖)≤
      ∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator (fun k=>
        ∫⁻z : ConeCoordinate,physicalGeometryCutoffDensity s
          (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
          (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  classical
  have hW := (F.prefixAngular_regular hs hT hw zX).1.measurable
  have hH := F.coneGeometryCutoffTangent_continuousOn hs zX
  have he := F.partialCutoffLabelCost_triangle hs hT zX Q hH hW hJ
  rw [coneGeometryCutoffTangent_pullback] at he
  rw [he]
  apply (F.partialCutoffTriangle_boundary_sum hs hT zX Q hH hW hJ hJT hq N hP).trans
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}
  · simp only [indicator_of_mem hk]
    apply lintegral_mono_ae
    have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
      ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV (representativeClosedBin T w k) hJ)] with z hz
    exact F.partialCutoffTriangle_geometry_density_le hw zX Q hJT hband _ hz
  · simp only [indicator_of_notMem hk]
    exact le_rfl

end RVM

end

end OAI
