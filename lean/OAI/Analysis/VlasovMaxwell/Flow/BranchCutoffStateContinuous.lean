import Mathlib
import OAI.Analysis.VlasovMaxwell.Geometry.CutoffState

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

lemma PhaseFlowOn.branchCutoffState_continuousAt {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈jointBranchDomain F.flow zX T) :
    ContinuousAt (fun q : ℝ×Phase=>branchCutoffState F.flow T zX q.2 q.1) p := by
  have hτ := F.joint_branch_continuousAt zX hp
  have ht := F.branch_time_mem zX p.2 hp.1 hp.2
  have hX := ((F.continuousOn_time zX).continuousAt
    (Icc_mem_nhds (hp.1.1.1.trans ht.1) ht.2)).comp (f := fun q : ℝ×Phase=>branchTime F.flow zX q.2 T q.1) hτ
  have hY := (F.joint p.2 p.1 hp.1.1).continuousAt
  have hr := hτ.sub continuousAt_fst
  have hr0 : branchTime F.flow zX p.2 T p.1-p.1≠0 := (sub_pos.mpr ht.1).ne'
  exact hr.prodMk (((hr.inv₀ hr0).smul (hX.fst.sub hY.fst)).prodMk
    (hY.snd.prodMk hX.snd))

lemma PhaseFlowOn.joint_momentumForce_continuousAt {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) {p : ℝ×Phase}
    (hp : p.1∈Ioo 0 T) :
    ContinuousAt (fun q : ℝ×Phase=>(lorentzField s.E s.B (q.1,F.flow q.2 q.1)).2) p := by
  have hF := (F.joint p.2 p.1 hp).continuousAt
  have hx := continuousAt_fst.prodMk hF.fst
  have hm : (p.1,(F.flow p.2 p.1).1)∈interior (Icc 0 T ×ˢ (univ : Set Vec)) := by
    rw [interior_prod_eq,interior_Icc,interior_univ]
    exact ⟨hp,mem_univ _⟩
  have hE := (hs.E_smooth.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hm)).comp (f := fun q : ℝ×Phase=>(q.1,(F.flow q.2 q.1).1)) hx
  have hB := (hs.B_smooth.continuousOn.continuousAt (mem_interior_iff_mem_nhds.mp hm)).comp (f := fun q : ℝ×Phase=>(q.1,(F.flow q.2 q.1).1)) hx
  have hu := (contDiff_velocity (k:=1)).continuous.continuousAt.comp hF.snd
  exact hE.add ((contDiff_cross (k:=1)).continuous.continuousAt.comp (hu.prodMk hB))

lemma PhaseFlowOn.branchCutoffStateRate_continuousAt {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) {p : ℝ×Phase}
    (hp : p∈jointBranchDomain F.flow zX T) :
    ContinuousAt (fun q : ℝ×Phase=>branchCutoffStateRate s.E s.B F.flow T zX q.2 q.1) p := by
  have hz := F.branchCutoffState_continuousAt zX hp
  have hτ := F.joint_branch_continuousAt zX hp
  have ht := F.branch_time_mem zX p.2 hp.1 hp.2
  have hn := F.branchDirection_norm zX p.2 hp.1 hp.2
  have ha := (contDiff_velocity (k:=1)).continuous.continuousAt.comp hz.snd.snd.snd
  have hu := (contDiff_velocity (k:=1)).continuous.continuousAt.comp hz.snd.snd.fst
  have hd := (continuousAt_const (y:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=1)).continuous.continuousAt.comp (hz.snd.fst.prodMk hu))
  have hD := (continuousAt_const (y:=(1:ℝ))).sub
    ((contDiff_dot_pair (k:=1)).continuous.continuousAt.comp (hz.snd.fst.prodMk ha))
  have hD0 : 1-dot (branchDirection F.flow zX p.2 T p.1)
      (velocity (F.flow zX (branchTime F.flow zX p.2 T p.1)).2)≠0 :=
    (cone_denom_pos _ _ hn).ne'
  have hρ := hd.div hD hD0
  have hr0 : branchTime F.flow zX p.2 T p.1-p.1≠0 := (sub_pos.mpr ht.1).ne'
  have hN := (hz.fst.inv₀ hr0).smul
    (((hρ.smul (ha.sub hz.snd.fst)).add hz.snd.fst).sub hu)
  have hKY := F.joint_momentumForce_continuousAt hs hp.1.1
  have hKX := ((F.momentumForce_continuousOn_closed hs zX).continuousAt
    (Icc_mem_nhds (hp.1.1.1.trans ht.1) ht.2)).comp (f := fun q : ℝ×Phase=>branchTime F.flow zX q.2 T q.1) hτ
  exact (hρ.sub continuousAt_const).prodMk (hN.prodMk (hKY.prodMk (hρ.smul hKX)))

lemma PhaseFlowOn.branchSelectedRate_measurable {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase)
    (Q : Set (Fin 4→ℕ)) :
    Measurable ((jointBranchDomain F.flow zX T).indicator
      (fun p : ℝ×Phase=>branchSelectedRate s.E s.B F.flow T zX p.2 Q p.1)) := by
  classical
  have hc : ContinuousOn (fun p : ℝ×Phase=>branchSelectedRate s.E s.B F.flow T zX p.2 Q p.1)
      (jointBranchDomain F.flow zX T) := by
    intro p hp
    have hsc := contDiffAt_stateCutoff T Q (z:=branchCutoffState F.flow T zX p.2 p.1)
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1)
      (F.branchDirection_norm zX p.2 hp.1 hp.2)
    exact (((hsc.continuousAt_fderiv (by simp)).comp (f := fun q : ℝ×Phase=>branchCutoffState F.flow T zX q.2 q.1)
      (F.branchCutoffState_continuousAt zX hp)).clm_apply
        (F.branchCutoffStateRate_continuousAt hs zX hp)).continuousWithinAt
  exact hc.measurable_piecewise continuousOn_const (F.isOpen_jointBranchDomain zX).measurableSet

lemma PhaseFlowOn.selectedCutoff_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    Measurable ((jointBranchDomain F.flow zX T).indicator
      (fun p : ℝ×Phase=>selectedDyadicCutoff Q (actualCutoffCoordinates F.flow T zX p.2 p.1))) := by
  classical
  have hc : ContinuousOn (fun p : ℝ×Phase=>stateCutoff T Q (branchCutoffState F.flow T zX p.2 p.1))
      (jointBranchDomain F.flow zX T) := by
    intro p hp
    exact ((contDiffAt_stateCutoff T Q (z:=branchCutoffState F.flow T zX p.2 p.1)
      (sub_pos.mpr (F.branch_time_mem zX p.2 hp.1 hp.2).1)
      (F.branchDirection_norm zX p.2 hp.1 hp.2)).continuousAt.comp (f := fun q : ℝ×Phase=>branchCutoffState F.flow T zX q.2 q.1)
        (F.branchCutoffState_continuousAt zX hp)).continuousWithinAt
  exact hc.measurable_piecewise continuousOn_const (F.isOpen_jointBranchDomain zX).measurableSet

lemma norm_fderiv_velocity_apply_le (v h : Vec) :
    ‖fderiv ℝ velocity v h‖≤‖h‖ := by
  apply ((fderiv ℝ velocity v).le_opNorm h).trans
  have hi : (q v)⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_q v)
  exact (mul_le_mul_of_nonneg_right (norm_fderiv_velocity_le v) (norm_nonneg h)).trans
    (by simpa using mul_le_mul_of_nonneg_right hi (norm_nonneg h))

lemma deficit_rate_bound {N V : ℝ→Vec} {n' v' : Vec} {t : ℝ}
    (hN : HasDerivAt N n' t) (hV : HasDerivAt V v' t) (hn : ‖N t‖=1) :
    |deriv (fun s=>1-dot (N s) (velocity (V s))) t|≤‖n'‖+‖v'‖ := by
  have hu := ((contDiff_velocity (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  have hd := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot hN hu)
  change HasDerivAt (fun s=>1-dot (N s) (velocity (V s))) _ t at hd
  rw [hd.deriv]
  simp only [zero_sub,abs_neg]
  apply (abs_add_le _ _).trans
  have ha : |dot (N t) (fderiv ℝ velocity (V t) v')|≤‖v'‖ := by
    apply (abs_dot_le _ _).trans
    rw [hn,one_mul]
    exact norm_fderiv_velocity_apply_le _ _
  have hb : |dot n' (velocity (V t))|≤‖n'‖ :=
    (abs_dot_le _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left (norm_velocity_lt_one (V t)).le (norm_nonneg n'))
  simpa only [Function.comp_apply] using add_le_add ha hb |>.trans (le_of_eq (add_comm _ _))

lemma physical_cutoff_coarse_rates {T t : ℝ} {V W N : ℝ→Vec} {R : ℝ→ℝ}
    {v' w' n' : Vec} {r' : ℝ} (hn : ‖N t‖=1) (hr : 0<R t)
    (hV : HasDerivAt V v' t) (hW : HasDerivAt W w' t)
    (hN : HasDerivAt N n' t) (hR : HasDerivAt R r' t) :
    ∑ i : Fin 4,|deriv (fun s=>physicalCutoffCoordinates T (R s) (N s) (V s) (W s) i) t /
        physicalCutoffCoordinates T (R t) (N t) (V t) (W t) i| ≤
      ‖v'‖+(‖n'‖+‖v'‖)/(2*(1-dot (N t) (velocity (V t))))+
        (‖n'‖+‖w'‖)/(2*(1-dot (N t) (velocity (W t))))+|r'|/R t := by
  have hq := ((contDiff_q (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  rw [fderiv_q_apply] at hq
  change HasDerivAt (fun s=>q (V s)) _ t at hq
  have hu := ((contDiff_velocity (k:=1)).differentiable one_ne_zero (V t)).hasFDerivAt.comp_hasDerivAt t hV
  have ha := ((contDiff_velocity (k:=1)).differentiable one_ne_zero (W t)).hasFDerivAt.comp_hasDerivAt t hW
  have hd := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot hN hu)
  change HasDerivAt (fun s=>1-dot (N s) (velocity (V s))) _ t at hd
  have hD := (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_dot hN ha)
  change HasDerivAt (fun s=>1-dot (N s) (velocity (W s))) _ t at hD
  have hdp := cone_denom_pos (V t) (N t) hn
  have hDp := cone_denom_pos (W t) (N t) hn
  have hed := angularCoordinate_log_deriv hd hdp
  have heD := angularCoordinate_log_deriv hD hDp
  have heq := inverseCoordinate_log_deriv hq (q_pos (V t))
  have hdb := deficit_rate_bound hN hV hn
  have hDb := deficit_rate_bound hN hW hn
  rw [hd.deriv] at hdb
  rw [hD.deriv] at hDb
  have hqb : |-dot (velocity (V t)) v'/q (V t)|≤‖v'‖ := by
    rw [abs_div,abs_neg,abs_of_pos (q_pos _)]
    apply (div_le_iff₀ (q_pos _)).mpr
    apply (abs_dot_le _ _).trans
    apply (mul_le_mul_of_nonneg_right (norm_velocity_lt_one _).le (norm_nonneg _)).trans
    rw [one_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_q _)
  have her : deriv (fun s=>R s/max 1 T) t/(R t/max 1 T)=r'/R t := by
    rw [(hR.div_const (max 1 T)).deriv]
    have hm : max 1 T≠0 := (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)).ne'
    field_simp
  simp only [Fin.sum_univ_succ,Fin.isValue,physicalCutoffCoordinates,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.sum_univ_zero,add_zero]
  rw [heq,hed,heD,her]
  rw [abs_div,abs_neg,abs_of_pos (q_pos _)] at hqb
  simp only [abs_div,abs_neg,abs_of_pos (q_pos _),abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hdp),
    abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hDp),abs_of_pos hr]
  have hddiv := div_le_div_of_nonneg_right hdb (mul_pos (by norm_num : (0:ℝ)<2) hdp).le
  have hDdiv := div_le_div_of_nonneg_right hDb (mul_pos (by norm_num : (0:ℝ)<2) hDp).le
  linarith

end RVM

end

end OAI
