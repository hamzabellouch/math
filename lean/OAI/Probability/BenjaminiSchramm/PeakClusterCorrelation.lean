import OAI.Probability.BenjaminiSchramm.LayerFrontierGeometry
import OAI.Probability.BenjaminiSchramm.LayerFreshSelection
import OAI.Probability.UnimodularPercolation.Splicing.GapCodes

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def restrictedSetHit (I : Set E) (A T : Set V) : Set (Set E) :=
  {ω | ∃ v ∈ A, ∃ t ∈ T, Conn G (ω ∩ I) v t}

def peakConnectionCell (I J : Set E) (u w : V) (S T : Set V) : Set (Set E) :=
  {ω | cluster G (ω ∩ I) u=S ∧
    Conn G ((ω ∩ J) ∩ internalEdges G S) u w ∧ Disjoint S T}

lemma peakConnectionCell_iff (I J : Set E) (hJI : J ⊆ I) (u w : V) (S T : Set V)
    (ω : Set E) :
    ω ∈ peakConnectionCell G I J u w S T ↔
      cluster G (ω ∩ I) u=S ∧ Conn G (ω ∩ J) u w ∧ Disjoint S T := by
  constructor
  · rintro ⟨hc,hw,hd⟩
    exact ⟨hc,conn_mono G Set.inter_subset_left hw,hd⟩
  · rintro ⟨hc,hw,hd⟩
    have hh := conn_restrict_cluster_of_subset G (ω ∩ I) u
      (fun e he => ⟨he.1,hJI he.2⟩) (mem_cluster_self G _ u) hw
    rw [hc] at hh
    exact ⟨hc,hh,hd⟩

lemma masked_internal_configuration_dependsOn (J : Set E) (S : Set V) :
    DependsOn (fun ω : Set E => (ω ∩ J) ∩ internalEdges G S) (ballIncidentEdges G S) := by
  intro ω η hωη
  ext e
  change ((ω e ∧ e ∈ J) ∧ e ∈ internalEdges G S) ↔
    ((η e ∧ e ∈ J) ∧ e ∈ internalEdges G S)
  by_cases he : e ∈ internalEdges G S
  · have hi : e ∈ ballIncidentEdges G S :=
      ⟨(G e).out.1,he _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩
    rw [hωη e hi]
  · simp only [he,and_false]

lemma peakConnectionCell_dependsOn (I J : Set E) (u w : V) (S T : Set V) :
    DependsOn (fun ω => ω ∈ peakConnectionCell G I J u w S T) (ballIncidentEdges G S) := by
  intro ω η hωη
  have hc := restricted_exactCluster_dependsOn G I u S hωη
  have hm := masked_internal_configuration_dependsOn G J S hωη
  change (cluster G (Set.inter ω I) u=S) = (cluster G (Set.inter η I) u=S) at hc
  change (Set.inter (Set.inter ω J) (internalEdges G S)) =
    (Set.inter (Set.inter η J) (internalEdges G S)) at hm
  change (cluster G (Set.inter ω I) u=S ∧
    Conn G (Set.inter (Set.inter ω J) (internalEdges G S)) u w ∧ Disjoint S T) =
      (cluster G (Set.inter η I) u=S ∧
    Conn G (Set.inter (Set.inter η J) (internalEdges G S)) u w ∧ Disjoint S T)
  rw [hc,hm]

lemma masked_exterior_configuration_dependsOn (I : Set E) (S : Set V) :
    DependsOn (fun ω : Set E => (ω ∩ I) ∩ internalEdges G Sᶜ) (ballIncidentEdges G S)ᶜ := by
  intro ω η hωη
  ext e
  change ((ω e ∧ e ∈ I) ∧ e ∈ internalEdges G Sᶜ) ↔
    ((η e ∧ e ∈ I) ∧ e ∈ internalEdges G Sᶜ)
  by_cases he : e ∈ internalEdges G Sᶜ
  · have hi : e ∈ (ballIncidentEdges G S)ᶜ := by
      rintro ⟨v,hv,hve⟩
      exact (he v hve) hv
    rw [hωη e hi]
  · simp only [he,and_false]

lemma peakConnectionCell_inter_hit (I J : Set E) (u w : V) (S A T : Set V) :
    peakConnectionCell G I J u w S T ∩ restrictedSetHit G I A T =
      peakConnectionCell G I J u w S T ∩
        restrictedSetHit G (I ∩ internalEdges G Sᶜ) A T := by
  ext ω
  constructor
  · rintro ⟨hc,v,hv,t,ht,hvt⟩
    have htn : t ∉ cluster G (ω ∩ I) u := by
      rw [hc.1]
      exact fun h => Set.disjoint_left.mp hc.2.2 h ht
    have hh := conn_restrict_away_from_cluster G (ω ∩ I) (ω ∩ I) Set.Subset.rfl
      u t v htn (conn_symm G _ hvt)
    rw [hc.1] at hh
    refine ⟨hc,v,hv,t,ht,?_⟩
    simpa only [Set.inter_assoc] using conn_symm G _ hh
  · rintro ⟨hc,v,hv,t,ht,hvt⟩
    exact ⟨hc,v,hv,t,ht,conn_mono G
      (Set.inter_subset_inter_right _ Set.inter_subset_left) hvt⟩

variable [Countable V] [Countable E]

lemma measurableSet_restrictedSetHit (I : Set E) (A T : Set V) :
    MeasurableSet (restrictedSetHit G I A T) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (Measurable.exists fun v => measurable_const.and
    (Measurable.exists fun t => measurable_const.and
      ((measurableSet_conn G v t).mem.comp hm))).setOf

lemma measurableSet_peakConnectionCell (I J : Set E) (u w : V) (S T : Set V) :
    MeasurableSet (peakConnectionCell G I J u w S T) := by
  have hm : Measurable (fun ω : Set E => (ω ∩ J) ∩ internalEdges G S) :=
    measurable_set_iff.mpr fun e => ((measurable_set_mem e).and measurable_const).and measurable_const
  exact (measurableSet_restricted_exactCluster G I u S).inter
    ((((measurableSet_conn G u w).mem.comp hm).and measurable_const).setOf)

omit [Countable V] [Countable E] in
lemma restrictedSetHit_exterior_dependsOn (I : Set E) (A T S : Set V) :
    DependsOn (fun ω => ω ∈ restrictedSetHit G (I ∩ internalEdges G Sᶜ) A T)
      (ballIncidentEdges G S)ᶜ := by
  intro ω η hωη
  have hh := masked_exterior_configuration_dependsOn G I S hωη
  change Set.inter (Set.inter ω I) (internalEdges G Sᶜ) =
    Set.inter (Set.inter η I) (internalEdges G Sᶜ) at hh
  have hh' : Set.inter ω (Set.inter I (internalEdges G Sᶜ)) =
      Set.inter η (Set.inter I (internalEdges G Sᶜ)) :=
    (Set.inter_assoc ω I (internalEdges G Sᶜ)).symm.trans
      (hh.trans (Set.inter_assoc η I (internalEdges G Sᶜ)))
  exact congrArg (fun ξ : Set E => ∃ v ∈ A, ∃ t ∈ T, Conn G ξ v t) hh'

lemma peakConnectionCell_hit_probability (p : unitInterval)
    (I J : Set E) (u w : V) (S A T : Set V) :
    law p (peakConnectionCell G I J u w S T ∩ restrictedSetHit G I A T) ≤
      law p (peakConnectionCell G I J u w S T)*law p (restrictedSetHit G I A T) := by
  rw [peakConnectionCell_inter_hit]
  have hlaw : CriticalPercolation.BernoulliProduct.law (fun _ : E => p) = law p :=
    CriticalPercolation.BernoulliProduct.law_const p
  rw [←hlaw]
  rw [CriticalPercolation.BernoulliProduct.measure_inter_of_separate_blocks (fun _ : E => p)
    (ballIncidentEdges G S) _ _ (measurableSet_peakConnectionCell G I J u w S T)
      (measurableSet_restrictedSetHit G _ A T) (peakConnectionCell_dependsOn G I J u w S T)
        (restrictedSetHit_exterior_dependsOn G I A T S)]
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro ω ⟨v,hv,t,ht,hvt⟩
  exact ⟨v,hv,t,ht,conn_mono G (Set.inter_subset_inter_right _ Set.inter_subset_left) hvt⟩

end Percolation.BenjaminiSchramm

end

end OAI
