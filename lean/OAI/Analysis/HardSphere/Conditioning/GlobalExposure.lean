import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalAssembly

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {E I : Type*} [MeasurableSpace E] [Fintype I]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

def blockExpose (p : I → Prop) (z : E × (∀i,X i)) :
    E × (∀i : {i // ¬p i},X i) := (z.1,fun i ↦ z.2 i)

omit [Fintype I] in
lemma blockExpose_measurable (p : I → Prop) : Measurable (blockExpose (E:=E) (X:=X) p) :=
  measurable_fst.prodMk (Measurable.of_eval fun i ↦
    (measurable_pi_apply i.val).comp measurable_snd)

omit [MeasurableSpace E] [Fintype I] in
lemma blockExpose_glue (p : I → Prop) [DecidablePred p] :
    blockExpose (E:=E) (X:=X) p ∘ blockGlue p = Prod.fst := by
  funext z
  apply Prod.ext
  · rfl
  funext i
  simp [blockExpose,blockGlue,MeasurableEquiv.piEquivPiSubtypeProd,i.property]

lemma exposedLaw_marginal (μ : Measure E) [SFinite μ]
    (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I → Prop) [DecidablePred p] {B : Set (E × (∀i,X i))}
    (hB : MeasurableSet B) :
    exposedLaw μ ν p B = ((μ.prod (Measure.pi ν)).restrict B).map (blockExpose p) := by
  have : SFinite (exposedLaw μ ν p B) := by unfold exposedLaw; infer_instance
  rw [←exposed_block_reconstruct μ ν p hB,
    Measure.map_map (blockExpose_measurable p) (blockGlue_measurable p),blockExpose_glue]
  symm
  exact fiberNormalize_fst (exposedLaw μ ν p B)
    (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i))
    (hB.preimage (blockGlue_measurable p)) (exposed_block_positive μ ν p hB)

lemma exposedLaw_mass (μ : Measure E) [SFinite μ]
    (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I → Prop) [DecidablePred p] {B : Set (E × (∀i,X i))}
    (hB : MeasurableSet B) :
    exposedLaw μ ν p B univ = ((μ.prod (Measure.pi ν)).restrict B) univ := by
  rw [exposedLaw_marginal μ ν p hB,Measure.map_apply (blockExpose_measurable p)
    MeasurableSet.univ,preimage_univ]

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
attribute [local instance] Classical.propDecidable

abbrev AllocatedDatum (E I A : Type*) (X : I → Type*) :=
  E × (I → Bool) × A × (∀i,X i)

def fillOutside (p : I → Prop) (x₀ : ∀i,X i) (x : ∀i : {i // ¬p i},X i) : ∀i,X i :=
  fun i ↦ if h : p i then x₀ i else x ⟨i,h⟩

omit [Fintype I] in
lemma fillOutside_measurable (p : I → Prop) (x₀ : ∀i,X i) :
    Measurable (fillOutside p x₀) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : p i
  · simpa only [fillOutside,dite_eq_left hi] using
      (measurable_const : Measurable (fun _ : ∀i : {i // ¬p i},X i ↦ x₀ i))
  · simpa only [fillOutside,dite_eq_right hi] using (measurable_pi_apply (⟨i,hi⟩ : {i // ¬p i}))

def branchDatum (p : A → I → Prop) (x₀ : ∀i,X i) (a : A) (b : I → Bool)
    (w : E × (∀i : {i // ¬p a i},X i)) : AllocatedDatum E I A X :=
  (w.1,b,a,fillOutside (p a) x₀ w.2)

omit [Fintype I] [Fintype A] [MeasurableSingletonClass A] in
lemma branchDatum_measurable (p : A → I → Prop) (x₀ : ∀i,X i) (a : A) (b : I → Bool) :
    Measurable (branchDatum (E:=E) p x₀ a b) :=
  measurable_fst.prodMk (measurable_const.prodMk (measurable_const.prodMk
    ((fillOutside_measurable (p a) x₀).comp measurable_snd)))

def allocationDatum (flag : ∀i,E × X i → Bool) (p : A → I → Prop) (x₀ : ∀i,X i)
    (z : (E × (∀i,X i)) × A) : AllocatedDatum E I A X :=
  (z.1.1,(fun i ↦ flag i (z.1.1,z.1.2 i)),z.2,
    fun i ↦ if p z.2 i then x₀ i else z.1.2 i)

omit [Fintype I] in
lemma allocationDatum_measurable (flag : ∀i,E × X i → Bool)
    (hflag : ∀i,Measurable (flag i)) (p : A → I → Prop) (x₀ : ∀i,X i) :
    Measurable (allocationDatum flag p x₀) := by
  apply measurable_fst.fst.prodMk
  apply Measurable.prodMk
  · exact Measurable.of_eval fun i ↦ (hflag i).comp
      (measurable_fst.fst.prodMk ((measurable_pi_apply i).comp measurable_fst.snd))
  apply measurable_snd.prodMk
  apply Measurable.of_eval
  intro i
  exact Measurable.ite (measurable_snd ((Set.to_countable {a : A | p a i}).measurableSet))
    measurable_const ((measurable_pi_apply i).comp measurable_fst.snd)

omit [MeasurableSpace E] [Fintype I] [∀i,MeasurableSpace (X i)]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma allocationDatum_branch (flag : ∀i,E × X i → Bool) (p : A → I → Prop)
    (x₀ : ∀i,X i) (a : A) (b : I → Bool) (z : E × (∀i,X i))
    (hz : z ∈ flagEvent flag b) :
    allocationDatum flag p x₀ (z,a) = branchDatum p x₀ a b (blockExpose (p a) z) := by
  have hb : (fun i ↦ flag i (z.1,z.2 i)) = b := funext hz
  simp only [allocationDatum,branchDatum,blockExpose,hb]
  congr 3

def allocatedDatumLaw (μ : Measure E) [SFinite μ]
    (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (flag : ∀i,E × X i → Bool) (hflag : ∀i,Measurable (flag i))
    (κ : Kernel (E × (I → Bool)) A) [IsMarkovKernel κ]
    (p : A → I → Prop) (x₀ : ∀i,X i) (B : Set (E × (∀i,X i))) :
    Measure (AllocatedDatum E I A X) :=
  (((μ.prod (Measure.pi ν)).restrict B).compProd
    (κ.comap (fun z ↦ (z.1,fun i ↦ flag i (z.1,z.2 i)))
      (measurable_fst.prodMk (Measurable.of_eval fun i ↦
        (hflag i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))))).map
    (allocationDatum flag p x₀)

lemma allocatedDatumLaw_branches (μ : Measure E) [SFinite μ]
    (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (flag : ∀i,E × X i → Bool) (hflag : ∀i,Measurable (flag i))
    (κ : Kernel (E × (I → Bool)) A) [IsMarkovKernel κ]
    (p : A → I → Prop) (x₀ : ∀i,X i)
    {B : Set (E × (∀i,X i))} (hB : MeasurableSet B) :
    allocatedDatumLaw μ ν flag hflag κ p x₀ B =
      ∑ b, ∑ a, (exposedLaw (allocationBase μ κ b a) ν (p a)
        (B ∩ flagEvent flag b)).map (branchDatum p x₀ a b) := by
  have hd := allocationDatum_measurable flag hflag p x₀
  have hf : Measurable (fun z : E × (∀i,X i) ↦ fun i ↦ flag i (z.1,z.2 i)) :=
    Measurable.of_eval fun i ↦ (hflag i).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  unfold allocatedDatumLaw
  rw [←allocated_flag_joint μ (Measure.pi ν) κ _ hf hB]
  simp only [Measure.map_finset_sum' hd.aemeasurable]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [exposedLaw_marginal _ _ _ (hB.inter (flagEvent_measurable flag hflag b)),
    Measure.map_map (branchDatum_measurable p x₀ a b) (blockExpose_measurable (p a)),
    Measure.map_map hd measurable_prodMk_right]
  simp only [allocationBase, flagEvent, ←funext_iff]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (hB.inter (measurableSet_eq_fun hf measurable_const))] with z hz
  exact allocationDatum_branch flag p x₀ a b z (fun i ↦ congrFun hz.2 i)

omit [Fintype A] [MeasurableSingletonClass A] in
lemma allocatedDatumLaw_probability (μ : Measure E) [SFinite μ]
    (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (flag : ∀i,E × X i → Bool) (hflag : ∀i,Measurable (flag i))
    (κ : Kernel (E × (I → Bool)) A) [IsMarkovKernel κ]
    (p : A → I → Prop) (x₀ : ∀i,X i) (B : Set (E × (∀i,X i)))
    [IsProbabilityMeasure ((μ.prod (Measure.pi ν)).restrict B)] :
    IsProbabilityMeasure (allocatedDatumLaw μ ν flag hflag κ p x₀ B) := by
  unfold allocatedDatumLaw
  infer_instance

end HardSphere.Comparison

namespace HardSphere.Groups
open Comparison Wiener Bridge Sampling
attribute [local instance] Classical.propDecidable

abbrev GroupDatum (N K M G : ℕ) (L : Length) :=
  AllocatedDatum (BridgeEndpoints N L) (Fin N) (GridAllocation N K (G*M))
    (fun _ ↦ Bridge.Noise)

def groundDatumLaw {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (ψ : Jet N L) (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (g : Fin G) :
    Measure (GroupDatum N K M G L) :=
  allocatedDatumLaw (endpointWeightedBase ψ t) (fun _ : Fin N ↦ Bridge.law)
    (eligibilityFlag (K:=K) m r R C S s₀ t u)
    (fun i ↦ eligibilityFlag_measurable m r R C S s₀ t u i)
    (gridAllocationKernel hL (G*M)) (fun a i ↦ i∈groupUnion g a)
    (fun _ ↦ 0) (labelInteraction N L r t)

lemma groundDatumLaw_probability {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    {ψ : Jet N L} (r : ℝ) (hψ : IsGroundVector N L r ψ)
    (m : ℕ) (R C S s₀ t : ℝ) (ht : 0≤t) (u : Time) (g : Fin G) :
    IsProbabilityMeasure (groundDatumLaw (M:=M) hL ψ m r R C S s₀ t u g) := by
  have := hψ.groundPathLaw_probability ht
  have : IsProbabilityMeasure (((endpointWeightedBase ψ t).prod
      (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict (labelInteraction N L r t)) := by
    constructor
    have h := congrArg (fun μ : Measure (ConfigurationPath N L) ↦ μ univ)
      (genuine_ground_label_bridge ψ r t)
    simpa only [Measure.map_apply (labelBridgePath_measurable N L t)
      MeasurableSet.univ,preimage_univ,measure_univ] using h
  exact allocatedDatumLaw_probability _ _ _ _ _ _ _ _

end HardSphere.Groups
end
end

end OAI
