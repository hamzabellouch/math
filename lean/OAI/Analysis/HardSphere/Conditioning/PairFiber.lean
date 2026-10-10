import Mathlib
import OAI.Analysis.HardSphere.Bridges.JointCollision
import OAI.Analysis.HardSphere.Geometry.EndpointLift
import OAI.Analysis.HardSphere.Conditioning.ProductNormalize

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I E : Type*} [Fintype I] [MeasurableSpace E]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]
attribute [local instance] Classical.propDecidable

def pairEvent (C : ∀i j,X i→X j→Prop) : Set (∀i,X i) :=
  {v | ∀i j,i≠j→C i j (v i) (v j)}

def frozenCompatible (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (w : ∀i : {i // ¬p i},X i) : Prop :=
  ∀i j : {i // ¬p i},i≠j→C i j (w i) (w j)

def individualFiber (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (flag : ∀i,X i→Bool) (b : I→Bool)
    (w : ∀i : {i // ¬p i},X i) (i : {i // p i}) : Set (X i) :=
  {v | flag i v=b i ∧ ∀j : {j // ¬p j},C i j v (w j) ∧ C j i (w j) v}

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma shifted_fiber (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (flag : ∀i,X i→Bool) (b : I→Bool)
    (w : ∀i : {i // ¬p i},X i) (v : ∀i : {i // p i},X i) :
    (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
      (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i) ↔
    frozenCompatible p C w ∧ (∀i : {i // ¬p i},flag i (w i)=b i) ∧
      v∈pairEvent (fun i j : {i // p i} ↦ C i j) ∩ univ.pi (individualFiber p C flag b w) := by
  constructor
  · rintro ⟨hp,hf⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro i j hij
      have hne : i.val≠j.val := fun he ↦ hij (Subtype.ext he)
      simpa [pairEvent,i.property,j.property] using hp i j hne
    · intro i
      simpa only [dite_eq_right i.property] using hf i
    · intro i j hij
      have hne : i.val≠j.val := fun he ↦ hij (Subtype.ext he)
      simpa only [dite_eq_left i.property,dite_eq_left j.property] using hp i j hne
    · intro i _
      constructor
      · simpa only [dite_eq_left i.property] using hf i
      · intro j
        have hne : i.val≠j.val := by intro h; exact j.property (h ▸ i.property)
        constructor
        · simpa only [dite_eq_left i.property,dite_eq_right j.property] using hp i j hne
        · simpa only [dite_eq_left i.property,dite_eq_right j.property] using hp j i hne.symm
  · rintro ⟨hout,hflag,hpair,hown⟩
    constructor
    · intro i j hij
      by_cases hi : p i <;> by_cases hj : p j
      · simpa only [dite_eq_left hi,dite_eq_left hj] using hpair ⟨i,hi⟩ ⟨j,hj⟩ (fun h ↦ hij (congrArg Subtype.val h))
      · simpa only [dite_eq_left hi,dite_eq_right hj] using ((hown ⟨i,hi⟩ (mem_univ _)).2 ⟨j,hj⟩).1
      · simpa only [dite_eq_right hi,dite_eq_left hj] using ((hown ⟨j,hj⟩ (mem_univ _)).2 ⟨i,hi⟩).2
      · simpa only [dite_eq_right hi,dite_eq_right hj] using hout ⟨i,hi⟩ ⟨j,hj⟩ (fun h ↦ hij (congrArg Subtype.val h))
    · intro i
      by_cases hi : p i
      · simpa only [dite_eq_left hi] using (hown ⟨i,hi⟩ (mem_univ _)).1
      · simpa only [dite_eq_right hi] using hflag ⟨i,hi⟩

lemma pairEvent_measurable (C : ∀i j,X i→X j→Prop)
    (hC : ∀i j,MeasurableSet {z : X i×X j | C i j z.1 z.2}) :
    MeasurableSet (pairEvent C) := by
  simp only [pairEvent,ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
    MeasurableSet.iInter fun (_ : i≠j) ↦ (hC i j).preimage ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

lemma individualFiber_measurable (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (hC : ∀i j,MeasurableSet {z : X i×X j | C i j z.1 z.2})
    (flag : ∀i,X i→Bool) (hflag : ∀i,Measurable (flag i)) (b : I→Bool)
    (w : ∀i : {i // ¬p i},X i) (i : {i // p i}) :
    MeasurableSet (individualFiber p C flag b w i) := by
  have he : individualFiber p C flag b w i={v | flag i v=b i} ∩
      ⋂j : {j // ¬p j}, {v | C i j v (w j)} ∩ {v | C j i (w j) v} := by
    ext v
    simp [individualFiber]
  rw [he]
  apply (measurableSet_eq_fun (hflag i) measurable_const).inter
  apply MeasurableSet.iInter
  intro j
  exact ((hC i j).preimage (measurable_id.prodMk measurable_const)).inter
    ((hC j i).preimage (measurable_const.prodMk measurable_id))

lemma positive_product_factors (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (S : ∀i,Set (X i)) (B : Set (∀i,X i))
    (h : (Measure.pi ν) (B∩univ.pi S)≠0) : ∀i,ν i (S i)≠0 := by
  have hpi : (Measure.pi ν) (univ.pi S)≠0 := ne_of_gt ((pos_iff_ne_zero.mpr h).trans_le (measure_mono inter_subset_right))
  rw [Measure.pi_pi] at hpi
  exact fun i ↦ (Finset.prod_ne_zero_iff.mp hpi) i (Finset.mem_univ i)

lemma conditional_pair_fiber (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (hC : ∀i j,MeasurableSet {z : X i×X j | C i j z.1 z.2})
    (flag : ∀i,X i→Bool) (hflag : ∀i,Measurable (flag i)) (b : I→Bool)
    (w : ∀i : {i // ¬p i},X i)
    (ν : ∀i : {i // p i},Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (hpos : (Measure.pi ν) {v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
      (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i)}≠0) :
    frozenCompatible p C w ∧
      (∀i,ν i (individualFiber p C flag b w i)≠0) ∧
      conditionedMeasure (Measure.pi ν)
        {v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
          (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i)}=
      conditionedMeasure
        (Measure.pi fun i ↦ conditionedMeasure (ν i) (individualFiber p C flag b w i))
        (pairEvent (fun i j : {i // p i} ↦ C i j)) := by
  have he : {v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
          (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i)}=
      pairEvent (fun i j : {i // p i} ↦ C i j) ∩ univ.pi (individualFiber p C flag b w) := by
    obtain ⟨v,hv⟩ := nonempty_of_measure_ne_zero hpos
    obtain ⟨hout,hf,_⟩ := (shifted_fiber p C flag b w v).mp hv
    ext u
    exact (shifted_fiber p C flag b w u).trans (by simp only [hout,hf,implies_true,true_and])
  rw [he] at hpos ⊢
  obtain ⟨v,hv⟩ := nonempty_of_measure_ne_zero hpos
  have hout : frozenCompatible p C w := by
    have hv' : v∈{v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
          (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i)} := by rw [he]; exact hv
    exact ((shifted_fiber p C flag b w v).mp hv').1
  have hnormal := positive_product_factors ν (individualFiber p C flag b w) _ hpos
  exact ⟨hout,hnormal,condition_product_factorization ν _
    (individualFiber_measurable p C hC flag hflag b w) hnormal _
    (pairEvent_measurable _ (fun i j ↦ hC i j)) hpos⟩

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Bridge GaussianPacking Comparison
attribute [local irreducible] torusDistance leg

def noisePairAvoid {N : ℕ} {L : Length} (a t : ℝ) (e : BridgeEndpoints N L)
    (i j : Fin N) (β γ : Bridge.Noise) : Prop :=
  ¬TrialCollision a
    (projectCurve L (leg t (labelStartLift e j) (labelEndLift t e j) γ))
    (leg t (labelStartLift e i) (labelEndLift t e i) β)

lemma noisePairAvoid_measurable {N : ℕ} {L : Length} (a t : ℝ)
    (e : BridgeEndpoints N L) (i j : Fin N) :
    MeasurableSet {z : Bridge.Noise×Bridge.Noise | noisePairAvoid a t e i j z.1 z.2} := by
  exact ((jointCollision_closed (L:=L) a).measurableSet.preimage
    (((leg_continuous t _ _).comp continuous_fst).prodMk
      ((leg_continuous t _ _).comp continuous_snd)).measurable).compl

lemma labelInteraction_pair {N : ℕ} {L : Length} (a t : ℝ)
    (e : BridgeEndpoints N L) (β : Fin N→Bridge.Noise) :
    (e,β)∈labelInteraction N L a t ↔ β∈pairEvent (noisePairAvoid a t e) := by
  have hcoord (i : Fin N) (s : Time) :
      labelBridgePath N L t (e,β) s i =
        projectPoint L (leg t (labelStartLift e i) (labelEndLift t e i) (β i) s) := by
    exact congrArg (fun f : C(Time,Configuration 1 L) ↦ f s 0) (labelBridgePath_lift t e β i)
  change (∀X,X∈Set.range (labelBridgePath N L t (e,β))→X∈allowed N L a) ↔ _
  simp only [Set.forall_mem_range,allowed_iff_ne,pairEvent,mem_ofPred_eq,
    noisePairAvoid,TrialCollision,not_exists,not_le]
  constructor
  · intro h i j hij s
    change a<torusDistance L (projectPoint L (leg t (labelStartLift e i) (labelEndLift t e i) (β i) s)) (projectPoint L (leg t (labelStartLift e j) (labelEndLift t e j) (β j) s))
    rw [←hcoord i s,←hcoord j s]
    exact h s i j hij
  · intro h s i j hij
    rw [hcoord i s,hcoord j s]
    exact h i j hij s

attribute [local instance] Classical.propDecidable

lemma noise_blockGlue {N : ℕ} {L : Length} (p : Fin N→Prop)
    (w : BridgeEndpoints N L×({i // ¬p i}→Bridge.Noise))
    (v : {i // p i}→Bridge.Noise) :
    (blockGlue p (w,v)).2=(fun i ↦ if h : p i then v ⟨i,h⟩ else w.2 ⟨i,h⟩) := by
  funext i
  by_cases hi : p i
  · simpa only [dite_eq_left hi] using blockGlue_inside (X:=fun _ : Fin N ↦ Bridge.Noise) p w v ⟨i,hi⟩
  · simpa only [dite_eq_right hi] using blockGlue_outside (X:=fun _ : Fin N ↦ Bridge.Noise) p w v ⟨i,hi⟩

lemma noise_flag_fiber {N : ℕ} {L : Length} (a t : ℝ)
    (flag : Fin N→BridgeEndpoints N L×Bridge.Noise→Bool)
    (b : Fin N→Bool) (p : Fin N→Prop)
    (w : BridgeEndpoints N L×({i // ¬p i}→Bridge.Noise)) :
    {v | blockGlue p (w,v)∈labelInteraction N L a t ∩ flagEvent flag b}=
      {v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w.2 ⟨i,h⟩)∈pairEvent (noisePairAvoid a t w.1) ∧
        ∀i,flag i (w.1,if h : p i then v ⟨i,h⟩ else w.2 ⟨i,h⟩)=b i} := by
  ext v
  have hglue : blockGlue p (w,v)=
      (w.1,fun i ↦ if h : p i then v ⟨i,h⟩ else w.2 ⟨i,h⟩) := by
    apply Prod.ext
    · exact blockGlue_fst (X:=fun _ : Fin N ↦ Bridge.Noise) p w v
    · exact noise_blockGlue p w v
  simp only [Set.mem_ofPred_eq]
  rw [hglue]
  simp only [mem_ofPred_eq,mem_inter_iff,labelInteraction_pair,flagEvent]

lemma recorded_physical_fiber {N : ℕ} {L : Length} (μ : Measure (BridgeEndpoints N L)) [SFinite μ] (a t : ℝ)
    (flag : Fin N→BridgeEndpoints N L×Bridge.Noise→Bool)
    (hflag : ∀i,Measurable (flag i)) (b : Fin N→Bool) (p : Fin N→Prop) :
    ∀ᵐw ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
        (labelInteraction N L a t ∩ flagEvent flag b),
      frozenCompatible p (noisePairAvoid a t w.1) w.2 ∧
      (∀i : {i // p i},Bridge.law
        (individualFiber p (noisePairAvoid a t w.1) (fun j β ↦ flag j (w.1,β)) b w.2 i)≠0) ∧
      conditionedMeasure (Measure.pi fun _ : {i // p i} ↦ Bridge.law)
        {v | blockGlue p (w,v)∈labelInteraction N L a t ∩ flagEvent flag b}=
      conditionedMeasure (Measure.pi fun i : {i // p i} ↦
        conditionedMeasure Bridge.law
          (individualFiber p (noisePairAvoid a t w.1) (fun j β ↦ flag j (w.1,β)) b w.2 i))
        (pairEvent (fun i j : {i // p i} ↦ noisePairAvoid a t w.1 i j)) := by
  filter_upwards [exposed_block_positive μ
    (fun _ : Fin N ↦ Bridge.law) p
    ((labelInteraction_measurable N L a t).inter (flagEvent_measurable flag hflag b))] with w hw
  have he := noise_flag_fiber a t flag b p w
  rw [he] at hw ⊢
  exact conditional_pair_fiber p (noisePairAvoid a t w.1)
    (noisePairAvoid_measurable a t w.1) (fun i β ↦ flag i (w.1,β))
    (fun i ↦ (hflag i).comp (measurable_const.prodMk measurable_id)) b w.2
    (fun _ ↦ Bridge.law) (ne_of_gt hw)

end HardSphere

end
end

end

end OAI
