import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.PathLift
import OAI.Analysis.HardSphere.Orbitals.CellPartition
import OAI.Analysis.HardSphere.Conditioning.Sampling

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Allocation (m : ℕ) (I : Type*) := Option (Fin m ↪ I)
instance allocationMeasurable (m : ℕ) : MeasurableSpace (Allocation m I) := ⊤
instance allocationSingletons (m : ℕ) : MeasurableSingletonClass (Allocation m I) := ⟨fun _ ↦ trivial⟩
instance allocationFintype (m : ℕ) : Fintype (Allocation m I) := inferInstanceAs (Fintype (Option (Fin m↪I)))

def allocationPMF (E : Finset I) (m : ℕ) : PMF (Allocation m I) := by
  classical
  by_cases h : m≤E.card
  · haveI : Nonempty (Fin m↪E) := Function.Embedding.nonempty_of_card_le (by simpa using h)
    exact (PMF.uniformOfFintype (Fin m↪E)).map (fun f ↦ some (f.trans (Function.Embedding.subtype _)))
  · exact PMF.pure none

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_large (E : Finset I) (m : ℕ) (h : m≤E.card)
    [Nonempty (Fin m↪E)] :
    allocationPMF E m=(PMF.uniformOfFintype (Fin m↪E)).map (fun f ↦ some (f.trans (Function.Embedding.subtype _))) := by
  simp [allocationPMF,h]

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_small (E : Finset I) (m : ℕ) (h : ¬m≤E.card) :
    allocationPMF E m=PMF.pure none := by simp [allocationPMF,h]

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_support (E : Finset I) (m : ℕ) (a : Allocation m I)
    (h : a∈(allocationPMF E m).support) :
    ∀f,a=some f→∀k,f k∈E := by
  classical
  by_cases hm : m≤E.card
  · have : Nonempty (Fin m↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hm)
    rw [allocationPMF_large E m hm,PMF.support_map] at h
    obtain ⟨g,_,rfl⟩ := h
    intro f hf k
    have he : g.trans (Function.Embedding.subtype _)=f := Option.some.inj hf
    exact he ▸ (g k).property
  · rw [allocationPMF_small E m hm,PMF.support_pure] at h
    have ha : a=none := h
    simp only [ha,reduceCtorEq,false_implies,implies_true]

def allocationKernel (m : ℕ) : Kernel (Finset I) (Allocation m I) :=
  ⟨fun E ↦ (allocationPMF E m).toMeasure,measurable_of_countable _⟩
instance allocationKernel_markov (m : ℕ) : IsMarkovKernel (allocationKernel (I:=I) m) :=
  ⟨fun E ↦ by change IsProbabilityMeasure (allocationPMF E m).toMeasure; infer_instance⟩

omit [Fintype I] [DecidableEq I] in
lemma allocated_group_uniform (E : Finset I) (m q : ℕ) (h : m≤E.card)
    (group : Fin q↪Fin m) :
    (allocationPMF E m).map (Option.map (fun f ↦ group.trans f))=allocationPMF E q := by
  classical
  have hqm : q ≤ m := by simpa using Fintype.card_le_of_embedding group
  have hq : q≤E.card := hqm.trans h
  have : Nonempty (Fin m↪E) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  have : Nonempty (Fin q↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hq)
  rw [allocationPMF_large E m h,allocationPMF_large E q hq,PMF.map_comp]
  have hu := congrArg (fun P : PMF (Fin q↪E) ↦ P.map (fun f ↦ some (f.trans (Function.Embedding.subtype _))))
    (embedding_restriction_uniform (V:=E) group)
  rw [PMF.map_comp] at hu
  exact hu

lemma allocation_half_bad (E B : Finset I) (m : ℕ) (hE : 2*m≤E.card)
    (hB : 10*(E∩B).card≤E.card) :
    (allocationPMF E (2*m)).toMeasure
      {a | ∃f,a=some f ∧ m≤(Finset.univ.filter (fun k ↦ f k∈B)).card}≤
      ENNReal.ofReal ((2/5:ℝ)^m) := by
  classical
  have : Nonempty (Fin (2*m)↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hE)
  let : MeasurableSpace (Fin (2*m)↪E) := ⊤
  let : MeasurableSingletonClass (Fin (2*m)↪E) := ⟨fun _ ↦ trivial⟩
  by_cases hempty : E.Nonempty
  · have : Nonempty E := hempty.to_subtype
    rw [allocationPMF_large E (2*m) hE,←PMF.toMeasure_map _ _ (measurable_of_countable _)]
    rw [Measure.map_apply (measurable_of_countable _) (by exact MeasurableSet.of_discrete)]
    let bad : Set E := {i | i.val∈B}
    have hc : Fintype.card bad=(E∩B).card := by
      let equiv : bad ≃ (E∩B : Finset I) :=
        { toFun := fun i ↦ ⟨i.val.val,Finset.mem_inter.mpr ⟨i.val.property,i.property⟩⟩
          invFun := fun i ↦ ⟨⟨i.val,(Finset.mem_inter.mp i.property).1⟩,(Finset.mem_inter.mp i.property).2⟩
          left_inv := fun i ↦ by cases i; rfl
          right_inv := fun i ↦ by cases i; rfl }
      exact (Fintype.card_congr equiv).trans (Fintype.card_coe (E∩B))
    have hb : (Nat.card bad:ℝ)≤(Fintype.card E:ℝ)/10 := by
      rw [Nat.card_eq_fintype_card,hc,Fintype.card_coe]
      have hb' : (10:ℝ)*((E∩B).card:ℝ)≤(E.card:ℝ) := by exact_mod_cast hB
      linarith
    rw [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (by exact MeasurableSet.of_discrete)]
    have hset : (fun f : Fin (2*m)↪E ↦ some (f.trans (Function.Embedding.subtype _))) ⁻¹'
        {a : Allocation (2*m) I | ∃f,a=some f ∧ m≤(Finset.univ.filter (fun k ↦ f k∈B)).card}=
        {f : Fin (2*m)↪E | m≤(Finset.univ.filter (fun k ↦ f k∈bad)).card} := by
      ext f
      simp [bad]
    rw [hset]
    have he : ENNReal.ofReal ((2/5:ℝ)^m)=(2/5:ℝ≥0∞)^m := by
      rw [ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [he]
    convert uniform_half_bad (V:=E) m bad hb using 1
    congr 1
    ext f
    simp only [Set.mem_ofPred_eq]
    apply iff_of_eq
    congr 1
    congr 1
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  · have hz : E=∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hm : m=0 := by simp [hz] at hE; omega
    subst m
    simp only [pow_zero,ENNReal.ofReal_one]
    exact prob_le_one

end HardSphere.Sampling

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local irreducible] torusDistance

def Confined {L : Length} (v : Torus L) (ω : ConfigurationPath 1 L) : Prop :=
  ∀s : Time,torusDistance L (ω s 0) v≤10

lemma confined_closed {L : Length} (v : Torus L) : IsClosed {ω | Confined v ω} := by
  simp only [Confined,ofPred_forall]
  apply isClosed_iInter
  intro s
  apply isClosed_le _ continuous_const
  exact (torusDistance_continuous_pair L).comp (f:=fun ω : ConfigurationPath 1 L ↦ (ω s 0,v)) (by fun_prop)

def EndpointEligible {N K : ℕ} {L : Length} (v : Fin 3→Fin K) (s₀ : ℝ)
    (Y Z : Configuration N L) (i : Fin N) : Prop :=
  Y i∈centeredCell L (gridCenter L v) ∧
  torusDistance L (Z i) (gridCenter L v)≤3 ∧
  ∀j,j≠i→s₀<torusDistance L (Y i) (Y j) ∧ s₀<torusDistance L (Z i) (Z j)

lemma endpointEligible_measurable {N K : ℕ} {L : Length} (v : Fin 3→Fin K) (s₀ : ℝ) (i : Fin N) :
    MeasurableSet {p : Configuration N L×Configuration N L | EndpointEligible v s₀ p.1 p.2 i} := by
  have h₁ : MeasurableSet {p : Configuration N L×Configuration N L | p.1 i∈centeredCell L (gridCenter L v)} :=
    (centeredCell_measurable L _).preimage ((measurable_pi_apply i).comp measurable_fst)
  have h₂ : MeasurableSet {p : Configuration N L×Configuration N L | torusDistance L (p.2 i) (gridCenter L v)≤3} :=
    measurableSet_le ((torusDistance_continuous_pair L).measurable.comp
      (f:=fun p : Configuration N L×Configuration N L ↦ (p.2 i,gridCenter L v)) (by fun_prop)) measurable_const
  have h₃ : MeasurableSet {p : Configuration N L×Configuration N L | ∀j,j≠i→
      s₀<torusDistance L (p.1 i) (p.1 j) ∧ s₀<torusDistance L (p.2 i) (p.2 j)} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro hj
    exact (measurableSet_lt measurable_const ((torusDistance_continuous_pair L).measurable.comp
      (f:=fun p : Configuration N L×Configuration N L ↦ (p.1 i,p.1 j)) (by fun_prop))).inter
      (measurableSet_lt measurable_const ((torusDistance_continuous_pair L).measurable.comp
      (f:=fun p : Configuration N L×Configuration N L ↦ (p.2 i,p.2 j)) (by fun_prop)))
  exact h₁.inter (h₂.inter h₃)

def Eligible {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (v : Fin 3→Fin K) (i : Fin N) (ω : ConfigurationPath N L) : Prop :=
  EndpointEligible v s₀ (ω 0) (ω 1) i ∧
  PathCutoff.Regular m r R C u S (onePathAt i ω) ∧ Confined (gridCenter L v) (onePathAt i ω)

lemma eligible_measurable {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (v : Fin 3→Fin K) (i : Fin N) : MeasurableSet {ω | Eligible (L:=L) m r R C S s₀ u v i ω} :=
  ((endpointEligible_measurable v s₀ i).preimage
    ((continuous_eval_const 0).measurable.prodMk (continuous_eval_const 1).measurable)).inter
      (((PathCutoff.regular_measurable m r R C u S).preimage (onePathAt_continuous i).measurable).inter
        ((confined_closed (gridCenter L v)).measurableSet.preimage (onePathAt_continuous i).measurable))

def eligibleList {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (v : Fin 3→Fin K) (ω : ConfigurationPath N L) : Finset (Fin N) :=
  Finset.univ.filter (fun i ↦ Eligible m r R C S s₀ u v i ω)

lemma eligibleList_disjoint {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) (ω : ConfigurationPath N L)
    {v w : Fin 3→Fin K} (hvw : v≠w) :
    Disjoint (eligibleList m r R C S s₀ u v ω) (eligibleList m r R C S s₀ u w ω) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Set.disjoint_left.mp (centeredCell_disjoint hL hK hvw)
    (Finset.mem_filter.mp hi).2.1.1 (Finset.mem_filter.mp hj).2.1.1

lemma eligibleList_measurable {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (v : Fin 3→Fin K) : Measurable (eligibleList (N:=N) (L:=L) m r R C S s₀ u v) := by
  apply measurable_to_countable'
  intro a
  have h : eligibleList (N:=N) (L:=L) m r R C S s₀ u v ⁻¹' {a}=
      ⋂i : Fin N, {ω | (i∈a) ↔ Eligible m r R C S s₀ u v i ω} := by
    ext ω
    simp only [mem_preimage,mem_singleton_iff,mem_iInter,mem_ofPred_eq]
    constructor
    · intro h i
      rw [←h]
      simp [eligibleList]
    · intro h
      ext i
      simpa only [eligibleList,Finset.mem_filter,Finset.mem_univ,true_and] using (h i).symm
  rw [h]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i∈a
  · simpa only [hi,true_iff] using eligible_measurable (N:=N) (L:=L) m r R C S s₀ u v i
  · simpa only [hi,false_iff,←Set.compl_ofPred] using (eligible_measurable (N:=N) (L:=L) m r R C S s₀ u v i).compl

end HardSphere.Groups

end
end

end

end OAI
