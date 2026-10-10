import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability
import OAI.Probability.CriticalPercolation.Gluing.HonestChoice
import OAI.Probability.CriticalPercolation.Gluing.TrialSelection

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation

lemma measurableSet_finset_subset {Ω V : Type*} {m : MeasurableSpace Ω}
    (S : Ω → Set V) (hS : @Measurable Ω (Set V) m inferInstance S) (U : Finset V) :
    MeasurableSet[m] {ω | (U : Set V)⊆S ω} := by
  have he : {ω | (U : Set V)⊆S ω}=⋂ v∈U, {ω | v∈S ω} := by
    ext ω
    simp [Set.subset_def]
  rw [he]
  exact MeasurableSet.biInter U.countable_toSet (fun v _ =>
    ((measurable_pi_apply v).comp hS).setOf)

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma levelContacts_reachable (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    {v : V} (hv : v∈G.levelContacts π j o ω) : (G.openGraph ω).Reachable o v :=
  G.cluster_mono Set.inter_subset_left o hv.1

lemma levelContacts_nonempty_of_hit (π : V → ℤ) (j : ℤ) (o : V) (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hhit : ω∈G.hitEvent o {v | π v<j}) :
    (G.levelContacts π j o ω).Nonempty := by
  by_contra h
  have hd : G.contactDrop π j o ω=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨v,hv,w,hw,hend⟩
    exact h ⟨v,hv⟩
  have hc : Disjoint (G.contactDrop π j o ω) ω := by rw [hd]; exact Set.empty_disjoint _
  have he := G.cluster_eq_exterior_of_drop_closed π j o ho hcross ω hc
  obtain ⟨v,hv,hlt⟩ := hhit
  have hle : j ≤ π v := G.exteriorCluster_subset_level π j o ho ω (he ▸ hv)
  exact (not_le.mpr hlt) hle

lemma levelContacts_supply (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) (ω : Set E)
    (hne : (G.levelContacts π j o ω).Nonempty) (hfew : ω∉G.fewContacts π j o k) :
    ∃ S : Finset V, (S : Set V)⊆G.levelContacts π j o ω ∧ k ≤ S.card := by
  by_cases hfin : (G.levelContacts π j o ω).Finite
  · refine ⟨hfin.toFinset,by simp,?_⟩
    by_contra hcard
    exact hfew ⟨hfin.toFinset,hfin.coe_toFinset.symm,
      by simpa using hne,lt_of_not_ge hcard⟩
  · obtain ⟨S,hS,hSfin,hcard⟩ := Set.Infinite.exists_subset_ncard_eq hfin k
    exact ⟨hSfin.toFinset,by simpa using hS,by simpa [Set.ncard_eq_toFinset_card S hSfin] using hcard.ge⟩

variable [Countable V] [Countable E]
def manyContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | (G.levelContacts π j o ω).Nonempty}\G.fewContacts π j o k

lemma measurableSet_manyContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) :
    MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] (G.manyContacts π j o k) := by
  apply MeasurableSet.diff _ (G.measurableSet_fewContacts π j o k)
  have he : {ω | (G.levelContacts π j o ω).Nonempty}=⋃ v : V, {ω | v∈G.levelContacts π j o ω} := by
    ext ω
    simp [Set.Nonempty]
  rw [he]
  exact MeasurableSet.iUnion (fun v =>
    @Measurable.setOf (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _
      ((measurable_pi_apply v).comp (G.measurable_levelContacts π j o)))

theorem honest_contact_selection (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (hk : M*N ≤ k)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (s : V → ℝ) (s₀ K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ v, π v=j → s₀ ≤ s v ∧ s v ≤ 1) (hN : K ≤ N*s₀) :
    ∃ d : Set E → Finset V,
      (∀ U, MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] {ω | d ω=U}) ∧
      ∀ ω∈G.manyContacts π j o k,
        (d ω : Set V)⊆G.levelContacts π j o ω ∧
        (d ω : Set V).Pairwise (fun v w => ¬C v w) ∧
        K ≤ ∑ v∈d ω, s v ∧ (∑ v∈d ω, s v) ≤ K+1 := by
  let P := fun (ω : Set E) (U : Finset V) =>
    (U : Set V)⊆G.levelContacts π j o ω ∧
    (U : Set V).Pairwise (fun v w => ¬C v w) ∧
    K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1
  have hm (U : Finset V) : MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] {ω | P ω U} :=
    (measurableSet_finset_subset _ (G.measurable_levelContacts π j o) U).inter (MeasurableSet.const _)
  obtain ⟨d,hd,hgood⟩ := @exists_honest_selector (Set E) (Finset V)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance inferInstance P hm
  refine ⟨d,hd,?_⟩
  intro ω hω
  apply hgood
  obtain ⟨S,hS,hcard⟩ := G.levelContacts_supply π j o k ω hω.1 hω.2
  have hb : ∀ v∈S, (S.filter (C v)).card ≤ M := by
    intro v _hv
    have hh : (S.filter (C v) : Set V)⊆{w | C v w} := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hz := (Set.ncard_le_ncard hh (hfinite v)).trans (hbound v)
    simpa only [Set.ncard_coe_finset] using hz
  obtain ⟨U,hU,hsep,hlo,hhi⟩ := separated_weighted_trials C hrefl hsymm M N hM S hb
    (hk.trans hcard) s s₀ K hK (fun v hv => hs v (hS hv).2) hN
  exact ⟨U,(fun _ hv => hS (hU hv)),hsep,hlo,hhi⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
