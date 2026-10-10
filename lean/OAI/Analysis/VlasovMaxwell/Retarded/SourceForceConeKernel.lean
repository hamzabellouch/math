import Mathlib
import OAI.Analysis.VlasovMaxwell.Population.RepresentativeCosts
import OAI.Analysis.VlasovMaxwell.Regularity.IntegralBallPolarFlip

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

private lemma SmoothClassicalPrefix.sourceForceEnergyPrefix
    {datum : Datum} {solution : Solution} {horizon : ℝ}
    (hs : SmoothClassicalPrefix datum solution horizon) : EnergyPrefix solution horizon := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro time ht position momentum
    have hh := (hs.equations time ht.1.le ht.2).1 position momentum
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro time ht position
    have he := (hs.equations time ht.1.le ht.2).2.1 position
    have hb := (hs.equations time ht.1.le ht.2).2.2.1 position
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

def sourceForceConeKernel (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (p : ConeKernelState) : Vec :=
  normalisedSignedForce (p.1.1-p.1.2) (velocity (α zX p.1.1).2)
    (velocity p.2.2.2) p.2.1 (sourceAcceleration s (p.1.2,p.2.2))

lemma PhaseFlowOn.actualLabelSignedForce_eq_normalised {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) :
    actualLabelSignedForce s F.flow zX T=
      labelConeKernel s F.flow zX T (sourceForceConeKernel s F.flow zX) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hr : branchTime F.flow zX p.2 T p.1-p.1≠0 :=
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1).ne'
    have hn := F.branchDirection_norm zX p.2 hp.1 hp.2
    simp only [actualLabelSignedForce,labelConeKernel,indicator_of_mem hp,
      sourceForceConeKernel,labelKernelState,normalisedSignedForce_eq _ _ _ _ hr
        (cone_denom_pos _ _ hn).ne' (cone_denom_pos _ _ hn).ne']
    rw [smul_comm (s.f (0,p.2)),smul_smul,←mul_pow,inv_mul_cancel₀ hr,one_pow,one_smul]
  · simp only [actualLabelSignedForce,labelConeKernel,indicator_of_notMem hp]

lemma labelConeKernel_receiver_weight (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (A : ConeKernelState→Vec) (ψ : ℝ→ℝ) (p : ℝ×Phase) :
    labelConeKernel s α zX T (fun q=>ψ q.1.1 • A q) p=
      ψ (labelReceiverTime α zX T p) • labelConeKernel s α zX T A p := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelConeKernel,labelReceiverTime,indicator_of_mem hp,labelKernelState]
    rw [smul_comm (s.f (0,p.2)),smul_comm ((branchTime α zX p.2 T p.1-p.1)⁻¹^2)]
  · simp only [labelConeKernel,indicator_of_notMem hp,smul_zero]

lemma SmoothClassicalPrefix.weighted_retarded_force_label {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) {ψ : ℝ→ℝ}
    (hψ : ContinuousOn ψ (Icc 0 T)) :
    (∫t in Ioo (0:ℝ) T,ψ t •
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
      (4*Real.pi)⁻¹ • ∫p,ψ (labelReceiverTime F.flow zX T p) •
        actualLabelSignedForce s F.flow zX T p := by
  let A : ConeKernelState→Vec := fun p=>ψ p.1.1 • sourceForceConeKernel s F.flow zX p
  have hA : ContinuousOn A (coneKernelDomain T) :=
    (hψ.comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).smul
      (F.normalised_source_force_continuousOn hs.sourceForceEnergyPrefix zX)
  have hlabel : (fun p=>ψ (labelReceiverTime F.flow zX T p) • actualLabelSignedForce s F.flow zX T p)=
      labelConeKernel s F.flow zX T A := by
    funext p
    rw [F.actualLabelSignedForce_eq_normalised zX]
    exact (labelConeKernel_receiver_weight s F.flow zX T _ ψ p).symm
  rw [hlabel,F.labelConeKernel_triangle_integral hs.sourceForceEnergyPrefix hT zX hA,
    F.triangleConeKernel_integral_sphere hs.sourceForceEnergyPrefix hT zX hA,←integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [hs.retarded_force_source_polar ht.1 ht.2 _ _ (norm_velocity_lt_one _),add_sub_cancel_left]
  rw [smul_comm]
  congr 1
  rw [←integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    rw [←integral_smul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro σ hσ
    dsimp only
    rw [smul_comm,←integral_smul]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ (fun v=>by
      dsimp only [A,sourceForceConeKernel]
      exact smul_comm _ _ _))

def unselectedLabelSignedForce (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) : Vec :=
  (1-labelSelectedCutoff α zX T Q p) •
    (ψ (labelReceiverTime α zX T p) • actualLabelSignedForce s α zX T p)

lemma split_label_force (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (p : ℝ×Phase) :
    ψ (labelReceiverTime α zX T p) • actualLabelSignedForce s α zX T p=
      unselectedLabelSignedForce s α zX T Q ψ p+selectedLabelSignedForce s α zX T Q ψ p := by
  rw [unselectedLabelSignedForce,selectedLabelSignedForce,labelWeight,mul_smul,
    smul_comm (ψ (labelReceiverTime α zX T p)),←add_smul]
  simp

lemma PhaseFlowOn.weightedLabelSignedForce_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {ψ : ℝ→ℝ} (hψ : Measurable ψ) (hψb : ∀t∈Icc 0 T,|ψ t|≤1) :
    Integrable (fun p=>ψ (labelReceiverTime F.flow zX T p) • actualLabelSignedForce s F.flow zX T p) := by
  apply (F.actualLabelSignedForce_integrable hs zX).bdd_smul 1
    (hψ.comp (F.labelReceiverTime_measurable zX)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p=>by
    simpa only [Real.norm_eq_abs,Function.comp_apply] using hψb _ (F.labelReceiverTime_mem hT zX p))

lemma PhaseFlowOn.unselectedLabelSignedForce_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} (hψ : Measurable ψ) (hψb : ∀t∈Icc 0 T,|ψ t|≤1) :
    Integrable (unselectedLabelSignedForce s F.flow zX T Q ψ) := by
  have he : unselectedLabelSignedForce s F.flow zX T Q ψ=
      (fun p=>ψ (labelReceiverTime F.flow zX T p) • actualLabelSignedForce s F.flow zX T p)-
        selectedLabelSignedForce s F.flow zX T Q ψ := by
    funext p
    exact (eq_sub_iff_add_eq.mpr (split_label_force s F.flow zX T Q ψ p).symm)
  rw [he]
  exact (F.weightedLabelSignedForce_integrable hs hT zX hψ hψb).sub
    (F.selectedLabelSignedForce_integrable hs hT zX Q hψ hψb)

lemma PhaseFlowOn.split_label_force_integral {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0) :
    (∫p,ψ (labelReceiverTime F.flow zX T p) • actualLabelSignedForce s F.flow zX T p)=
      (∫p,unselectedLabelSignedForce s F.flow zX T Q ψ p)+
      (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ
        (fun _=>ContinuousLinearMap.id ℝ Vec) z)+
      ∫p,selectedLabelCosts s F.flow zX T Q ψ p := by
  simp_rw [split_label_force s F.flow zX T Q ψ]
  rw [integral_add (F.unselectedLabelSignedForce_integrable hs hT zX Q hψ.continuous.measurable hψb)
    (F.selectedLabelSignedForce_integrable hs hT zX Q hψ.continuous.measurable hψb)]
  rw [show (∫p,selectedLabelSignedForce s F.flow zX T Q ψ p)=
      ∫σ : ℝ,∫z : Phase,selectedLabelSignedForce s F.flow zX T Q ψ (σ,z) from
        integral_prod _ (F.selectedLabelSignedForce_integrable hs hT zX Q hψ.continuous.measurable hψb),
    F.selected_signed_fubini hs hT zX Q hψ hψb hψT,
    ←integral_prod _ (F.selectedLabelCosts_integrable hs hT zX Q hψ hψb),add_assoc]
  rw [←Measure.volume_eq_prod]

lemma SmoothClassicalPrefix.selected_force_decomposition {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0) :
    (∫t in Ioo (0:ℝ) T,ψ t •
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
      (4*Real.pi)⁻¹ • ((∫p,unselectedLabelSignedForce s F.flow zX T Q ψ p)+
        (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ
          (fun _=>ContinuousLinearMap.id ℝ Vec) z)+∫p,selectedLabelCosts s F.flow zX T Q ψ p) := by
  rw [hs.weighted_retarded_force_label hT F zX hψ.continuous.continuousOn,
    F.split_label_force_integral hs.sourceForceEnergyPrefix hT zX Q hψ hψb hψT]

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma triangleConeKernel_receiver_multiplier (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    (p : ConeCoordinate×Vec) :
    triangleConeKernel s α zX T (fun q=>W q.1.1 (A q)) p=
      W p.1.1 (triangleConeKernel s α zX T A p) := by
  classical
  by_cases hp : p∈trianglePhaseDomain T
  · simp only [triangleConeKernel,indicator_of_mem hp,triangleKernelState,map_smul]
  · simp only [triangleConeKernel,indicator_of_notMem hp,map_zero]

lemma labelConeKernel_receiver_multiplier (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (A : ConeKernelState→Vec) (W : ℝ→Vec→L[ℝ]Vec)
    (p : ℝ×Phase) :
    labelConeKernel s α zX T (fun q=>W q.1.1 (A q)) p=
      W (labelReceiverTime α zX T p) (labelConeKernel s α zX T A p) := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelConeKernel,labelReceiverTime,indicator_of_mem hp,labelKernelState,map_smul]
  · simp only [labelConeKernel,indicator_of_notMem hp,map_zero]

lemma PhaseFlowOn.triangleConeKernel_multiplier_fiber {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {A : ConeKernelState→Vec} (hA : ContinuousOn A (coneKernelDomain T))
    {W : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T)) :
    (∫p,triangleConeKernel s F.flow zX T (fun q=>W q.1.1 (A q)) p ∂trianglePhaseMeasure)=
      ∫t : ℝ,W t (∫p : ℝ×Sphere,∫v : Vec,
        triangleConeKernel s F.flow zX T A ((t,p),v) ∂volume ∂volume.prod sphereMeasure) := by
  let g := triangleConeKernel s F.flow zX T A
  let B : ConeKernelState→Vec := fun q=>W q.1.1 (A q)
  have hB : ContinuousOn B (coneKernelDomain T) :=
    (hW.comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).clm_apply hA
  have hg := F.triangleConeKernel_integrable hs hT zX hA
  have hb := F.triangleConeKernel_integrable hs hT zX hB
  have hi : Integrable (fun z : ConeCoordinate=>∫v : Vec,g (z,v))
      (volume.prod (volume.prod sphereMeasure)) := hg.integral_prod_left
  rw [trianglePhaseMeasure,integral_prod _ hb,integral_prod _ hb.integral_prod_left]
  apply integral_congr_ae
  have hvi := Measure.ae_ae_of_ae_prod hg.prod_right_ae
  filter_upwards [hi.prod_right_ae,hvi] with t ht hvt
  rw [←(W t).integral_comp_comm ht]
  apply integral_congr_ae
  filter_upwards [hvt] with p hp
  rw [←(W t).integral_comp_comm hp]
  apply integral_congr_ae
  exact ae_of_all _ (fun v=>triangleConeKernel_receiver_multiplier s F.flow zX T A W ((t,p),v))

lemma PhaseFlowOn.triangleConeKernel_fiber_sphere {s : Solution} {T t : ℝ}
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (A : ConeKernelState→Vec)
    (ht : t∈Ioo 0 T)
    (hi : Integrable (fun p : ℝ×Sphere=>∫v : Vec,
      triangleConeKernel s F.flow zX T A ((t,p),v)) (volume.prod sphereMeasure)) :
    (∫p : ℝ×Sphere,∫v : Vec,triangleConeKernel s F.flow zX T A ((t,p),v)
      ∂volume ∂volume.prod sphereMeasure)=
      ∫n : Sphere,∫σ in Ioo (0:ℝ) t,
        (1-dot n.1 (velocity (F.flow zX t).2)) •
        ∫v : Vec,s.f (σ,((F.flow zX t).1-(t-σ) • n.1,v)) •
          A ((t,σ),(n.1,((F.flow zX t).1-(t-σ) • n.1,v))) ∂volume ∂volume ∂sphereMeasure := by
  classical
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    rw [←integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    exact ae_of_all _ (fun σ=>by
      dsimp only
      by_cases hσ : σ∈Ioo 0 t
      · rw [indicator_of_mem hσ,←integral_smul]
        apply integral_congr_ae
        exact ae_of_all _ (fun v=>by
          have hp : ((t,σ,n),v)∈trianglePhaseDomain T := ⟨ht,hσ⟩
          simp only [triangleConeKernel,indicator_of_mem hp,triangleKernelState])
      · rw [indicator_of_notMem hσ]
        have hz : ∀v : Vec,triangleConeKernel s F.flow zX T A ((t,σ,n),v)=0 := by
          intro v
          have hp : ((t,σ,n),v)∉trianglePhaseDomain T := fun hp=>hσ hp.2
          simp only [triangleConeKernel,indicator_of_notMem hp]
        simp only [hz,integral_zero]))

lemma SmoothClassicalPrefix.multiplier_retarded_force_label {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {W : ℝ→Vec→L[ℝ]Vec} (hW : ContinuousOn W (Icc 0 T)) :
    (∫t in Ioo (0:ℝ) T,W t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
      (4*Real.pi)⁻¹ • ∫p,W (labelReceiverTime F.flow zX T p)
        (actualLabelSignedForce s F.flow zX T p) := by
  classical
  let A := sourceForceConeKernel s F.flow zX
  have hA : ContinuousOn A (coneKernelDomain T) :=
    F.normalised_source_force_continuousOn hs.sourceForceEnergyPrefix zX
  let B : ConeKernelState→Vec := fun q=>W q.1.1 (A q)
  have hB : ContinuousOn B (coneKernelDomain T) :=
    (hW.comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).clm_apply hA
  have hlabel : (fun p=>W (labelReceiverTime F.flow zX T p)
        (actualLabelSignedForce s F.flow zX T p))=labelConeKernel s F.flow zX T B := by
    funext p
    rw [F.actualLabelSignedForce_eq_normalised zX]
    exact (labelConeKernel_receiver_multiplier s F.flow zX T A W p).symm
  rw [hlabel,F.labelConeKernel_triangle_integral hs.sourceForceEnergyPrefix hT zX hB]
  dsimp only [B]
  rw [F.triangleConeKernel_multiplier_fiber hs.sourceForceEnergyPrefix hT zX hA hW,
    ←integral_smul,←integral_indicator measurableSet_Ioo]
  have hg := F.triangleConeKernel_integrable hs.sourceForceEnergyPrefix hT zX hA
  have hi : Integrable (fun z : ConeCoordinate=>∫v : Vec,triangleConeKernel s F.flow zX T A (z,v))
      (volume.prod (volume.prod sphereMeasure)) := hg.integral_prod_left
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with t ht
  by_cases htT : t∈Ioo 0 T
  · rw [indicator_of_mem htT,F.triangleConeKernel_fiber_sphere zX A htT ht,
      hs.retarded_force_source_polar htT.1 htT.2 _ _ (norm_velocity_lt_one _),add_sub_cancel_left,
      map_smul]
    rfl
  · rw [indicator_of_notMem htT]
    have hz : ∀p : ℝ×Sphere,∀v : Vec,triangleConeKernel s F.flow zX T A ((t,p),v)=0 := by
      intro p v
      have hp : ((t,p),v)∉trianglePhaseDomain T := fun hp=>htT hp.1
      simp only [triangleConeKernel,indicator_of_notMem hp]
    simp only [hz,integral_zero,map_zero,smul_zero]

lemma PhaseFlowOn.split_multiplier_force_integral {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : Continuous W) (hW' : Continuous W')
    (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫p,W (labelReceiverTime F.flow zX T p)
      (ψ (labelReceiverTime F.flow zX T p) • actualLabelSignedForce s F.flow zX T p))=
      (∫p,W (labelReceiverTime F.flow zX T p) (unselectedLabelSignedForce s F.flow zX T Q ψ p))+
      (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z)+
      ∫p,selectedMultiplierCosts s F.flow zX T Q ψ W W' p := by
  have hiU := F.integrable_receiver_multiplier hT zX hW
    (F.unselectedLabelSignedForce_integrable hs hT zX Q hψ.continuous.measurable hψb)
  obtain ⟨hiK,hiC⟩ := F.selectedMultiplier_integrable hs hT zX Q hψ hψb hW hW'
  simp_rw [split_label_force s F.flow zX T Q ψ,map_add]
  change Integrable (fun p=>W (labelReceiverTime F.flow zX T p)
    (selectedLabelSignedForce s F.flow zX T Q ψ p)) at hiK
  rw [integral_add hiU hiK]
  change _+(∫p,selectedMultiplierForce s F.flow zX T Q ψ W p)=_
  rw [show (∫p,selectedMultiplierForce s F.flow zX T Q ψ W p)=
      ∫σ : ℝ,∫z : Phase,selectedMultiplierForce s F.flow zX T Q ψ W (σ,z) from
        integral_prod _ hiK,
    F.selected_multiplier_fubini hs hT zX Q hψ hψb hψT hW hW' hWd,
    ←integral_prod _ hiC,add_assoc]
  rw [←Measure.volume_eq_prod]

lemma SmoothClassicalPrefix.selected_multiplier_decomposition {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t|≤1) (hψT : ψ T=0)
    {W W' : ℝ→Vec→L[ℝ]Vec} (hW : Continuous W) (hW' : Continuous W')
    (hWd : ∀t∈Ioo 0 T,HasDerivAt W (W' t) t) :
    (∫t in Ioo (0:ℝ) T,ψ t • W t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
      (4*Real.pi)⁻¹ • ((∫p,W (labelReceiverTime F.flow zX T p)
        (unselectedLabelSignedForce s F.flow zX T Q ψ p))+
        (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ W z)+
        ∫p,selectedMultiplierCosts s F.flow zX T Q ψ W W' p) := by
  have he := hs.multiplier_retarded_force_label hT F zX
    (W:=fun t=>ψ t • W t) (hψ.continuous.smul hW).continuousOn
  change (∫t in Ioo (0:ℝ) T,ψ t • W t
    (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
      boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
    (4*Real.pi)⁻¹ • ∫p,ψ (labelReceiverTime F.flow zX T p) •
      W (labelReceiverTime F.flow zX T p) (actualLabelSignedForce s F.flow zX T p) at he
  rw [he]
  congr 1
  simp_rw [←map_smul]
  exact F.split_multiplier_force_integral hs.sourceForceEnergyPrefix hT zX Q hψ hψb hψT hW hW' hWd

end RVM

end

end OAI
