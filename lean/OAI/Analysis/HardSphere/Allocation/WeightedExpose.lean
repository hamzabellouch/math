import Mathlib
import OAI.Analysis.HardSphere.Allocation.Allocation
import OAI.Analysis.HardSphere.Bridges.ReferenceHit
import OAI.Analysis.HardSphere.Conditioning.PairFiber

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {E J A : Type*} [MeasurableSpace E] [MeasurableSpace J] [MeasurableSpace A]
  [Fintype J] [Fintype A] [MeasurableSingletonClass A]

def allocationBase (μ : Measure E) (κ : Kernel (E×J) A) (b : J) (a : A) : Measure E :=
  μ.withDensity (fun e ↦ κ (e,b) {a})

instance allocationBase_sfinite (μ : Measure E) [SFinite μ]
    (κ : Kernel (E×J) A) (b : J) (a : A) : SFinite (allocationBase μ κ b a) := by
  unfold allocationBase
  infer_instance

omit [Fintype J] in
lemma allocationBase_sum (μ : Measure E) (κ : Kernel (E×J) A) [IsMarkovKernel κ] (b : J) :
    (∑a,allocationBase μ κ b a)=μ := by
  have hm (a : A) : Measurable (fun e ↦ κ (e,b) {a}) :=
    (κ.measurable_coe (measurableSet_singleton a)).comp (measurable_id.prodMk measurable_const)
  have hsum : (∑'a : A,fun e ↦ κ (e,b) {a})=(fun _ ↦ (1:ℝ≥0∞)) := by
    funext e
    rw [tsum_fintype,Finset.sum_apply]
    simp
  have h := withDensity_tsum (μ:=μ) hm
  rw [hsum,withDensity_const,one_smul,Measure.sum_fintype] at h
  exact h.symm

omit [Fintype J] in
lemma allocation_branch_sum {Y : Type*} [MeasurableSpace Y]
    (μ : Measure E) (κ : Kernel (E×J) A) [IsMarkovKernel κ] (b : J)
    (ν : Measure Y) [SFinite ν] {C : Set (E×Y)} (hC : MeasurableSet C) :
    (∑a,((allocationBase μ κ b a).prod ν).restrict C)=(μ.prod ν).restrict C := by
  have hprod := Measure.prod_sum_left (fun a ↦ allocationBase μ κ b a) ν
  simp only [Measure.sum_fintype] at hprod
  rw [allocationBase_sum] at hprod
  have hr := Measure.restrict_sum (fun a ↦ (allocationBase μ κ b a).prod ν) hC
  simp only [Measure.sum_fintype] at hr
  rw [←hr,←hprod]

variable {I : Type*} [Fintype I] {X : I→Type*} [∀i,MeasurableSpace (X i)]
attribute [local instance] Classical.propDecidable

lemma allocated_exposure_reconstruct (μ : Measure E) [SFinite μ]
    (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (κ : Kernel (E×J) A) [IsMarkovKernel κ] (p : A→I→Prop)
    {B : Set (E×(∀i,X i))} (hB : MeasurableSet B)
    (F : J→Set (E×(∀i,X i))) (hF : ∀j,MeasurableSet (F j))
    (hdis : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (hcover : (⋃j,F j)=univ) :
    (∑b,∑a,((exposedLaw (allocationBase μ κ b a) ν (p a) (B∩F b)).compProd
      (fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p a i} ↦ ν i))
        (blockEvent (p a) (B∩F b)))).map (blockGlue (p a)))=
      (μ.prod (Measure.pi ν)).restrict B := by
  have (b : J) (a : A) : SFinite (exposedLaw (allocationBase μ κ b a) ν (p a) (B∩F b)) := by
    unfold exposedLaw
    infer_instance
  simp_rw [exposed_block_reconstruct _ _ _ (hB.inter (hF _))]
  simp_rw [allocation_branch_sum μ κ _ (Measure.pi ν) (hB.inter (hF _))]
  exact restrict_finite_partition _ B F hF hdis hcover

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere
open Wiener Bridge Comparison
attribute [local instance] Classical.propDecidable

lemma genuine_ground_allocated_exposure {N : ℕ} {L : Length}
    (u : Jet N L) (a t : ℝ)
    (flag : Fin N→BridgeEndpoints N L×Bridge.Noise→Bool)
    (hflag : ∀i,Measurable (flag i))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (κ : Kernel (BridgeEndpoints N L×(Fin N→Bool)) A) [IsMarkovKernel κ]
    (p : A→Fin N→Prop) :
    (∑b,∑j,((exposedLaw (allocationBase (endpointWeightedBase u t) κ b j)
        (fun _ : Fin N ↦ Bridge.law) (p j)
        (labelInteraction N L a t∩flagEvent flag b)).compProd
      (fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p j i} ↦ Bridge.law))
        (blockEvent (p j) (labelInteraction N L a t∩flagEvent flag b)))).map
        (labelBridgePath N L t ∘ blockGlue (p j)))=groundPathLaw N L a t u := by
  have he := allocated_exposure_reconstruct (endpointWeightedBase u t)
    (fun _ : Fin N ↦ Bridge.law) κ p (labelInteraction_measurable N L a t)
    (flagEvent flag) (flagEvent_measurable flag hflag)
    (flagEvent_partition flag).1 (flagEvent_partition flag).2
  have hm := congrArg (fun μ ↦ Measure.map (labelBridgePath N L t) μ) he
  simp only [Measure.map_finset_sum' (labelBridgePath_measurable N L t).aemeasurable,
    Measure.map_map (labelBridgePath_measurable N L t) (blockGlue_measurable _)] at hm
  exact hm.trans (genuine_ground_label_bridge u a t)

lemma allocated_physical_fiber {N : ℕ} {L : Length} (u : Jet N L) (a t : ℝ)
    (flag : Fin N→BridgeEndpoints N L×Bridge.Noise→Bool)
    (hflag : ∀i,Measurable (flag i))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (κ : Kernel (BridgeEndpoints N L×(Fin N→Bool)) A) (p : A→Fin N→Prop)
    (b : Fin N→Bool) (j : A) :
    ∀ᵐw ∂exposedLaw (allocationBase (endpointWeightedBase u t) κ b j)
        (fun _ : Fin N ↦ Bridge.law) (p j)
        (labelInteraction N L a t∩flagEvent flag b),
      frozenCompatible (p j) (noisePairAvoid a t w.1) w.2 ∧
      (∀i : {i // p j i},Bridge.law
        (individualFiber (p j) (noisePairAvoid a t w.1)
          (fun k β ↦ flag k (w.1,β)) b w.2 i)≠0) ∧
      conditionedMeasure (Measure.pi fun _ : {i // p j i} ↦ Bridge.law)
        {v | blockGlue (p j) (w,v)∈labelInteraction N L a t∩flagEvent flag b}=
      conditionedMeasure (Measure.pi fun i : {i // p j i} ↦
        conditionedMeasure Bridge.law (individualFiber (p j) (noisePairAvoid a t w.1)
          (fun k β ↦ flag k (w.1,β)) b w.2 i))
        (pairEvent (fun i k : {i // p j i} ↦ noisePairAvoid a t w.1 i k)) :=
  recorded_physical_fiber _ a t flag hflag b (p j)

end HardSphere

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge CellOrbital Sampling Comparison
attribute [local instance] Classical.propDecidable

def ownPath {N : ℕ} {L : Length} (i : Fin N) (t : ℝ)
    (p : BridgeEndpoints N L×Bridge.Noise) : ConfigurationPath 1 L :=
  onePathAt i (labelBridgePath N L t (p.1,fun _ ↦ p.2))

lemma ownPath_measurable {N : ℕ} {L : Length} (i : Fin N) (t : ℝ) :
    Measurable (ownPath (L:=L) i t) :=
  (onePathAt_continuous i).measurable.comp
    ((labelBridgePath_measurable N L t).comp (by fun_prop))

lemma ownPath_eq {N : ℕ} {L : Length} (i : Fin N) (t : ℝ)
    (e : BridgeEndpoints N L) (β : Fin N→Bridge.Noise) :
    ownPath i t (e,β i)=onePathAt i (labelBridgePath N L t (e,β)) := by
  simp only [ownPath,labelBridgePath_lift]

def ownEligible {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) (p : BridgeEndpoints N L×Bridge.Noise) : Prop :=
  ∃v : Fin 3→Fin K, EndpointEligible v s₀ p.1.2 (bridgeEnd N L t p.1) i ∧
    PathCutoff.Regular m r R C u S (ownPath i t p) ∧ Confined (gridCenter L v) (ownPath i t p)

lemma ownEligible_measurable {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) : MeasurableSet {p | ownEligible (K:=K) (L:=L) m r R C S s₀ t u i p} := by
  simp only [ownEligible,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro v
  exact ((endpointEligible_measurable v s₀ i).preimage
    (measurable_snd.comp measurable_fst |>.prodMk ((bridgeEnd_continuous N L t).measurable.comp measurable_fst))).inter
      (((PathCutoff.regular_measurable m r R C u S).preimage (ownPath_measurable i t)).inter
        ((confined_closed (gridCenter L v)).measurableSet.preimage (ownPath_measurable i t)))

def eligibilityFlag {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) (p : BridgeEndpoints N L×Bridge.Noise) : Bool :=
  decide (ownEligible (K:=K) m r R C S s₀ t u i p)

lemma eligibilityFlag_measurable {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) : Measurable (eligibilityFlag (K:=K) (L:=L) m r R C S s₀ t u i) := by
  apply measurable_to_countable'
  intro b
  cases b
  · change MeasurableSet {p | decide (ownEligible (K:=K) m r R C S s₀ t u i p)=false}
    simpa only [decide_eq_false_iff_not,←Set.compl_ofPred]
      using (ownEligible_measurable (K:=K) (L:=L) m r R C S s₀ t u i).compl
  · change MeasurableSet {p | decide (ownEligible (K:=K) m r R C S s₀ t u i p)=true}
    simpa only [decide_eq_true_eq]
      using ownEligible_measurable (K:=K) (L:=L) m r R C S s₀ t u i

lemma exposed_endpoints {N : ℕ} {L : Length} (t : ℝ) (e : BridgeEndpoints N L) :
    ∀ᵐβ ∂(Measure.pi fun _ : Fin N ↦ Bridge.law),
      labelBridgePath N L t (e,β) 0=e.2 ∧
      labelBridgePath N L t (e,β) 1=bridgeEnd N L t e := by
  have he : ∀ᵐβ ∂(Measure.pi fun _ : Fin N ↦ Bridge.law),∀i : Fin N,
      leg t (labelStartLift e i) (labelEndLift t e i) (β i) 0=labelStartLift e i ∧
      leg t (labelStartLift e i) (labelEndLift t e i) (β i) 1=labelEndLift t e i :=
    ae_all_iff.mpr (fun i ↦ (measurePreserving_eval (fun _ : Fin N ↦ Bridge.law) i).quasiMeasurePreserving.ae
      (leg_endpoints_ae t _ _))
  filter_upwards [he] with β hβ
  constructor
  · ext i j
    have hi := congrFun (congrFun (congrArg (fun ω : ConfigurationPath 1 L ↦ ω 0) (labelBridgePath_lift t e β i)) 0) j
    change _=((leg t (labelStartLift e i) (labelEndLift t e i) (β i) 0) j : AddCircle L.val) at hi
    rw [(hβ i).1] at hi
    exact hi.trans (congrFun (congrFun (project_representative N L e.2) i) j)
  · ext i j
    have hi := congrFun (congrFun (congrArg (fun ω : ConfigurationPath 1 L ↦ ω 1) (labelBridgePath_lift t e β i)) 0) j
    change _=((leg t (labelStartLift e i) (labelEndLift t e i) (β i) 1) j : AddCircle L.val) at hi
    rw [(hβ i).2] at hi
    exact hi.trans (by
      change ((labelStartLift e i j+Real.sqrt (2*t)*e.1 (i,j):ℝ):AddCircle L.val)=_
      rw [QuotientAddGroup.mk_add]
      have hp := congrFun (congrFun (project_representative N L e.2) i) j
      change ((labelStartLift e i j:ℝ):AddCircle L.val)=e.2 i j at hp
      rw [hp]
      rfl)

def recordedList {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (v : Fin 3→Fin K)
    (p : BridgeEndpoints N L×(Fin N→Bool)) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ gridHome hL (p.1.2 i)=v ∧ p.2 i=true)

lemma recordedList_measurable {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (v : Fin 3→Fin K) :
    Measurable (recordedList (N:=N) hL v) := by
  apply measurable_to_countable'
  intro a
  have h : recordedList (N:=N) hL v ⁻¹' {a}=
      ⋂i : Fin N,{p | (i∈a) ↔ gridHome hL (p.1.2 i)=v ∧ p.2 i=true} := by
    ext p
    simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_iInter,Set.mem_ofPred_eq]
    constructor
    · intro h i
      rw [←h]
      simp [recordedList]
    · intro h
      ext i
      simpa only [recordedList,Finset.mem_filter,Finset.mem_univ,true_and] using (h i).symm
  rw [h]
  apply MeasurableSet.iInter
  intro i
  have hm : MeasurableSet {p : BridgeEndpoints N L×(Fin N→Bool) |
      gridHome hL (p.1.2 i)=v ∧ p.2 i=true} :=
    (measurableSet_eq_fun ((gridHome_measurable hL).comp (by fun_prop)) measurable_const).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)
  by_cases hi : i∈a
  · simpa only [hi,true_iff] using hm
  · simpa only [hi,false_iff,←Set.compl_ofPred] using hm.compl

lemma recordedList_eq {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (v : Fin 3→Fin K) (e : BridgeEndpoints N L)
    (β : Fin N→Bridge.Noise) (h0 : labelBridgePath N L t (e,β) 0=e.2)
    (h1 : labelBridgePath N L t (e,β) 1=bridgeEnd N L t e) :
    recordedList hL v (e,fun i ↦ eligibilityFlag (K:=K) m r R C S s₀ t u i (e,β i))=
      eligibleList m r R C S s₀ u v (labelBridgePath N L t (e,β)) := by
  ext i
  simp only [recordedList,eligibleList,Finset.mem_filter,Finset.mem_univ,true_and,
    eligibilityFlag,decide_eq_true_eq,ownEligible,Eligible,h0,h1,ownPath_eq]
  constructor
  · rintro ⟨hi,w,hw,hr,hc⟩
    have hw' : gridHome hL (e.2 i)=w := (gridHome_eq_iff hL hK _ _).mpr hw.1
    have hvw : w=v := hw'.symm.trans hi
    rw [hvw] at hw hc
    exact ⟨hw,hr,hc⟩
  · intro hv
    exact ⟨(gridHome_eq_iff hL hK _ _).mpr hv.1.1,v,hv⟩

end HardSphere.Groups

end
end

end

end OAI
