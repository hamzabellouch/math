import Mathlib
import OAI.Analysis.VlasovMaxwell.Retarded.CutoffRateMajorant

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

def actualLabelCutoffCost (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (p : ℝ×Phase) : Vec :=
  (jointBranchDomain α zX T).indicator
    (fun p=>branchSelectedRate s.E s.B α T zX p.2 Q p.1) p • actualLabelPrimitive s α zX T p

lemma PhaseFlowOn.actualLabelCutoffCost_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    Measurable (actualLabelCutoffCost s F.flow zX T Q) :=
  (F.branchSelectedRate_measurable hs zX Q).smul (F.actualLabelPrimitive_measurable hs zX)

lemma PhaseFlowOn.actualLabelCutoffCost_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    Integrable (actualLabelCutoffCost s F.flow zX T Q) := by
  classical
  obtain ⟨C,hC,hcb⟩ := dyadicFactor_log_derivative_bound
  let A := normalisedCutoffPrimitive s F.flow zX (5^4*C)
  have hA := F.normalisedCutoffPrimitive_continuousOn hs zX (5^4*C)
  apply (F.labelConeKernel_integrable hs zX hA).norm.mono'
    (F.actualLabelCutoffCost_measurable hs zX Q).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hj : p∈jointBranchDomain F.flow zX T := hp
    have hr : 0<branchTime F.flow zX p.2 T p.1-p.1 :=
      sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1
    have hb := F.branchSelectedRate_coarse_bound hs zX p.2 hp.1 hp.2 Q hC hcb
    have hv := cutoff_primitive_norm_bound hr (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2)
      (velocity (F.flow p.2 p.1).2) (branchDirection F.flow zX p.2 T p.1) hb
    rw [actualLabelCutoffCost,indicator_of_mem hj,actualLabelPrimitive,indicator_of_mem hp,
      labelConeKernel,indicator_of_mem hp]
    rw [smul_comm (branchSelectedRate s.E s.B F.flow T zX p.2 Q p.1) (s.f (0,p.2))]
    simp only [norm_smul,Real.norm_eq_abs] at hv ⊢
    rw [abs_of_nonneg (sq_nonneg ((branchTime F.flow zX p.2 T p.1-p.1)⁻¹))]
    convert mul_le_mul_of_nonneg_left hv (abs_nonneg (s.f (0,p.2))) using 1
    simp only [normalisedCutoffPrimitive,labelKernelState,norm_smul,Real.norm_eq_abs]
    ring
  · have hj : p∉jointBranchDomain F.flow zX T := hp
    simp only [actualLabelCutoffCost,indicator_of_notMem hj,zero_smul,norm_zero,labelConeKernel,
      indicator_of_notMem hp,le_refl]

def labelReceiverTime (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) : ℝ×Phase→ℝ :=
  (labelBranchDomain α zX T).indicator (fun p=>branchTime α zX p.2 T p.1)

lemma PhaseFlowOn.labelReceiverTime_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) : Measurable (labelReceiverTime F.flow zX T) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuousOn_const (F.isOpen_jointBranchDomain zX).measurableSet
  intro p hp
  exact (F.joint_branch_continuousAt zX hp).continuousWithinAt

lemma PhaseFlowOn.labelReceiverTime_mem {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) (p : ℝ×Phase) :
    labelReceiverTime F.flow zX T p∈Icc 0 T := by
  classical
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · rw [labelReceiverTime,indicator_of_mem hp]
    have ht := F.branch_time_mem zX p.2 hp.1 hp.2
    exact ⟨(hp.1.1.1.trans ht.1).le,ht.2.le⟩
  · simp only [labelReceiverTime,indicator_of_notMem hp,mem_Icc,le_refl,hT,and_self]

def labelSelectedCutoff (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (Q : Set (Fin 4→ℕ)) : ℝ×Phase→ℝ :=
  (jointBranchDomain α zX T).indicator
    (fun p=>selectedDyadicCutoff Q (actualCutoffCoordinates α T zX p.2 p.1))

lemma PhaseFlowOn.labelSelectedCutoff_bound {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (Q : Set (Fin 4→ℕ)) (p : ℝ×Phase) :
    |labelSelectedCutoff F.flow zX T Q p|≤1 := by
  classical
  by_cases hp : p∈jointBranchDomain F.flow zX T
  · rw [labelSelectedCutoff,indicator_of_mem hp]
    have ht := F.branch_time_mem zX p.2 hp.1 hp.2
    have hn := F.branchDirection_norm zX p.2 hp.1 hp.2
    have hm : selectedDyadicCutoff Q
        (actualCutoffCoordinates F.flow T zX p.2 p.1)∈Icc (0:ℝ) 1 := by
      apply selectedDyadicCutoff_mem_unit
      · exact physicalCutoffCoordinates_pos hn (sub_pos.mpr ht.1)
      · exact physicalCutoffCoordinates_le_one hn
          (by linarith [le_max_right (1:ℝ) T,hp.1.1.1])
    exact (abs_of_nonneg hm.1).le.trans hm.2
  · simp only [labelSelectedCutoff,indicator_of_notMem hp,abs_zero,zero_le_one]

def actualLabelRatePrimitive (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (p : ℝ×Phase) : Vec :=
  branchRate α zX p.2 T p.1 • actualLabelPrimitive s α zX T p

def normalisedRatePrimitive (α : Phase→ℝ→Phase) (zX : Phase) (p : ConeKernelState) : Vec :=
  ((1-dot p.2.1 (velocity p.2.2.2))/(1-dot p.2.1 (velocity (α zX p.1.1).2))) •
    normalisedPrimitive (p.1.1-p.1.2) (velocity (α zX p.1.1).2) (velocity p.2.2.2) p.2.1

lemma PhaseFlowOn.normalisedRatePrimitive_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (normalisedRatePrimitive F.flow zX) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  have hn : Continuous (fun p : ConeKernelState=>p.2.1) := continuous_snd.fst
  have hD : ∀p∈coneKernelDomain T,1-dot p.2.1 (velocity (F.flow zX p.1.1).2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  have hr : ContinuousOn (fun p : ConeKernelState=>(1-dot p.2.1 (velocity p.2.2.2))/
      (1-dot p.2.1 (velocity (F.flow zX p.1.1).2))) (coneKernelDomain T) := by
    simp only [dot_eq_inner]
    exact (continuousOn_const.sub (hn.continuousOn.inner hu.continuousOn)).div
      (continuousOn_const.sub (hn.continuousOn.inner ha))
      (fun p hp=>by simpa only [dot_eq_inner] using hD p hp)
  refine hr.smul (continuousOn_normalisedPrimitive
    (continuous_fst.fst.sub continuous_fst.snd).continuousOn ha hu.continuousOn hn.continuousOn ?_ hD)
  intro p hp
  exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

lemma PhaseFlowOn.actualLabelRatePrimitive_eq {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (s : Solution) (zX : Phase) :
    actualLabelRatePrimitive s F.flow zX T =
      labelConeKernel s F.flow zX T (normalisedRatePrimitive F.flow zX) := by
  classical
  funext p
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · have hr : branchTime F.flow zX p.2 T p.1-p.1≠0 :=
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1).ne'
    rw [actualLabelRatePrimitive,actualLabelPrimitive,indicator_of_mem hp,labelConeKernel,indicator_of_mem hp]
    simp only [normalisedRatePrimitive,labelKernelState,normalisedPrimitive_eq _ _ _ hr]
    simp only [branchRate,smul_smul]
    congr 1
    simp only [branchDirection]
    field_simp
  · simp only [actualLabelRatePrimitive,actualLabelPrimitive,labelConeKernel,indicator_of_notMem hp,smul_zero]

lemma PhaseFlowOn.actualLabelRatePrimitive_integrable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Integrable (actualLabelRatePrimitive s F.flow zX T) := by
  rw [F.actualLabelRatePrimitive_eq s zX]
  exact F.labelConeKernel_integrable hs zX (F.normalisedRatePrimitive_continuousOn zX)

lemma PhaseFlowOn.actualLabelRatePrimitive_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    Measurable (actualLabelRatePrimitive s F.flow zX T) := by
  rw [F.actualLabelRatePrimitive_eq s zX]
  exact F.measurable_labelConeKernel hs zX (F.normalisedRatePrimitive_continuousOn zX)

end RVM

end

end OAI
