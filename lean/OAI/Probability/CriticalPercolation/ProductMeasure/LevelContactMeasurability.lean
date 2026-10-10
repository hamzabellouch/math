import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.Gluing.LevelContactGeometry
import OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

def finiteSetChoice {E : Type*} (S : Set E) : Finset E :=
  if h : S.Finite then h.toFinset else ∅

lemma finiteSetChoice_coe {E : Type*} {S : Set E} (hS : S.Finite) :
    (finiteSetChoice S : Set E)=S := by simp [finiteSetChoice,hS]

lemma finiteSetChoice_eq_iff {E : Type*} (S : Set E) (U : Finset E) :
    finiteSetChoice S=U ↔ S=(U : Set E) ∨ (¬S.Finite ∧ U=∅) := by
  by_cases hS : S.Finite
  · have hh : finiteSetChoice S=U ↔ S=(U : Set E) := by
      calc
        finiteSetChoice S=U ↔ (finiteSetChoice S : Set E)=(U : Set E) := Finset.coe_inj.symm
        _ ↔ S=(U : Set E) := by rw [finiteSetChoice_coe hS]
    simpa [hS] using hh
  · have hne : S≠(U : Set E) := fun h => hS (h ▸ U.finite_toSet)
    simp [finiteSetChoice,hS,hne,eq_comm]

lemma measurableSet_set_eq_const {Ω E : Type*} {m : MeasurableSpace Ω} [Countable E]
    (S : Ω → Set E) (hS : @Measurable Ω (Set E) m inferInstance S) (U : Set E) :
    MeasurableSet[m] {ω | S ω=U} := by
  let : MeasurableSpace Ω := m
  have he : {ω | S ω=U}={ω | ∀ e, e∈S ω ↔ e∈U} := by
    ext ω
    exact Set.ext_iff
  rw [he]
  exact (Measurable.forall (fun e => ((measurable_pi_apply e).comp hS).iff measurable_const)).setOf

lemma measurableSet_finiteSetChoice {Ω E : Type*} [MeasurableSpace Ω] [Countable E]
    (S : Ω → Set E) (hS : Measurable S) (U : Finset E) :
    MeasurableSet {ω | finiteSetChoice (S ω)=U} := by
  have hmfinite : MeasurableSet {ω | (S ω).Finite} := by
    have he : {ω | (S ω).Finite}=⋃ F : Finset E, {ω | S ω=(F : Set E)} := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
      exact ⟨fun h => ⟨h.toFinset,h.coe_toFinset.symm⟩,
        fun ⟨F,hF⟩ => hF ▸ F.finite_toSet⟩
    rw [he]
    exact MeasurableSet.iUnion (fun F => measurableSet_set_eq_const S hS _)
  simp_rw [finiteSetChoice_eq_iff]
  exact (measurableSet_set_eq_const S hS _).union
    (hmfinite.compl.inter (MeasurableSet.const _))

namespace BernoulliProduct
variable {E : Type*}
lemma measurable_inter_block (X : Set E) :
    @Measurable (Set E) (Set E) (blockSigma X) inferInstance (fun ω => ω∩X) := by
  have hh := measurable_forceOn_block Xᶜ (∅ : Set E)
  rw [compl_compl] at hh
  have he : forceOn Xᶜ (∅ : Set E)=(fun ω : Set E => ω∩X) := by
    unfold forceOn
    funext configuration
    apply Set.ext
    intro edge
    rw [Set.mem_inter_iff]
    simp only [Membership.mem, Set.Mem]
    split_ifs with hedge
    · exact ⟨False.elim, fun hmem => hedge hmem.2⟩
    · exact ⟨fun hmem => ⟨hmem, not_not.mp hedge⟩, And.left⟩
  rw [he] at hh
  exact hh
end BernoulliProduct

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma incident_ncard_le (S : Set V) (hS : S.Finite)
    (D : ℕ) (hD : ∀ v∈S, (G.incidentEdges {v}).ncard ≤ D) :
    (G.incidentEdges S).ncard ≤ S.ncard*D := by
  have he : G.incidentEdges S=⋃ v∈hS.toFinset, G.incidentEdges {v} := by
    ext e
    simp [incidentEdges]
  rw [he]
  calc
    _ ≤ ∑ v∈hS.toFinset, (G.incidentEdges {v}).ncard :=
      Finset.set_ncard_biUnion_le hS.toFinset _
    _ ≤ ∑ _v∈hS.toFinset, D := Finset.sum_le_sum (fun v hv => hD v (hS.mem_toFinset.mp hv))
    _ = _ := by simp [Set.ncard_eq_toFinset_card S hS]

lemma finite_contactDrop (hlocal : G.LocallyFinite) (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    (hS : (G.levelContacts π j o ω).Finite) : (G.contactDrop π j o ω).Finite :=
  (G.finite_incident hlocal hS).subset (G.contactDrop_subset_incident π j o ω)

lemma contactDrop_ncard_le (hlocal : G.LocallyFinite) (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    (hS : (G.levelContacts π j o ω).Finite) (D : ℕ)
    (hD : ∀ v∈G.levelContacts π j o ω, (G.incidentEdges {v}).ncard ≤ D) :
    (G.contactDrop π j o ω).ncard ≤ (G.levelContacts π j o ω).ncard*D :=
  (Set.ncard_le_ncard (G.contactDrop_subset_incident π j o ω) (G.finite_incident hlocal hS)).trans
    (G.incident_ncard_le _ hS D hD)

variable [Countable V] [Countable E]
lemma measurable_exteriorCluster (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set V) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.exteriorCluster π j o) :=
  (G.measurable_cluster o).comp (measurable_inter_block _)

lemma measurable_levelContacts (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set V) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.levelContacts π j o) := by
  refine @Measurable.of_eval (Set E) V (fun _ => Prop)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) (fun _ => inferInstance) _ ?_
  intro v
  exact @Measurable.and (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _
    ((measurable_pi_apply v).comp (G.measurable_exteriorCluster π j o)) measurable_const

lemma measurable_contactDrop (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.contactDrop π j o) := by
  refine @Measurable.of_eval (Set E) E (fun _ => Prop)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) (fun _ => inferInstance) _ ?_
  intro e
  exact @Measurable.exists (Set E) V (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _ (fun v =>
    @Measurable.and (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _
      ((measurable_pi_apply v).comp (G.measurable_levelContacts π j o)) measurable_const)

def fewContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | ∃ U : Finset V, G.levelContacts π j o ω=(U : Set V) ∧ U.Nonempty ∧ U.card<k}

lemma measurableSet_fewContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) :
    MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] (G.fewContacts π j o k) := by
  have he : G.fewContacts π j o k=⋃ U : Finset V,
      ({ω | G.levelContacts π j o ω=(U : Set V)}∩{_ω | U.Nonempty ∧ U.card<k}) := by
    ext ω
    simp [fewContacts]
  rw [he]
  exact MeasurableSet.iUnion (fun U =>
    (measurableSet_set_eq_const _ (G.measurable_levelContacts π j o) (U : Set V)).inter
      (MeasurableSet.const _))

omit [Countable V] [Countable E] in
lemma fewContacts_finite (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) (ω : Set E)
    (hω : ω∈G.fewContacts π j o k) :
    (G.levelContacts π j o ω).Finite ∧ (G.levelContacts π j o ω).Nonempty ∧
      (G.levelContacts π j o ω).ncard<k := by
  obtain ⟨U,hU,hne,hcard⟩ := hω
  rw [hU]
  exact ⟨U.finite_toSet,hne,by simpa using hcard⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
