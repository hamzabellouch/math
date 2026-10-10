import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.CutEdges
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelCutProbability
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal symmDiff Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def freshClusterBoundary (X : Set E) (v : V) (ω : Set E) : Set E :=
  G.cutEdges (G.cluster (ω∩X) v) \ X

lemma cutEdges_disjoint_cluster (ω : Set E) (v : V) :
    Disjoint (G.cutEdges (G.cluster ω v)) ω := by
  apply Set.disjoint_left.mpr
  rintro e ⟨x,y,he,hx,hy⟩ hω
  have hne : x ≠ y := fun h => hx (h ▸ hy)
  exact hx (hy.trans (SimpleGraph.Adj.reachable
    (show (G.openGraph ω).Adj x y from ⟨⟨e,hω,he⟩,hne⟩)).symm)

lemma finite_cutEdges (hl : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.cutEdges S).Finite := by
  apply (G.finite_incident hl hS).subset
  rintro e ⟨x,y,he,_,hy⟩
  exact ⟨y,hy,by rw [he]; simp⟩

lemma cluster_eq_restricted_of_fresh_closed (X : Set E) (v : V) (ω : Set E)
    (h : Disjoint (G.freshClusterBoundary X v ω) ω) :
    G.cluster ω v = G.cluster (ω∩X) v := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hn
    apply G.not_reachable_of_cut_closed (G.cluster (ω∩X) v) ω ?_ hn
      (SimpleGraph.Reachable.refl v) hx.symm
    intro e he hω
    by_cases hX : e∈X
    · exact Set.disjoint_left.mp (G.cutEdges_disjoint_cluster (ω∩X) v) he ⟨hω,hX⟩
    · exact Set.disjoint_left.mp h ⟨he,hX⟩ hω
  · exact G.cluster_mono Set.inter_subset_left v

lemma measurable_freshClusterBoundary [Countable V] [Countable E] (X : Set E) (v : V) :
    @Measurable (Set E) (Set E) (blockSigma X) inferInstance (G.freshClusterBoundary X v) := by
  let : MeasurableSpace (Set E) := blockSigma X
  refine Measurable.of_eval ?_
  intro e
  exact @Measurable.and (Set E) (blockSigma X) _ _
    (.exists fun x => .exists fun y => measurable_const.and
      ((((G.measurable_reachable v x).comp (measurable_inter_block X)).not).and
        ((G.measurable_reachable v y).comp (measurable_inter_block X)))) measurable_const

def smallFreshBoundary (X : Set E) (v : V) (M : ℕ) : Set (Set E) :=
  {ω | (G.cluster (ω∩X) v).Finite ∧ (G.freshClusterBoundary X v ω).ncard ≤ M}

lemma measurableSet_smallFreshBoundary [Countable V] [Countable E] (X : Set E) (v : V) (M : ℕ) :
    MeasurableSet[blockSigma X] (G.smallFreshBoundary X v M) := by
  have hf : MeasurableSet[blockSigma X] {ω | (G.cluster (ω∩X) v).Finite} := by
    let : MeasurableSpace (Set E) := blockSigma X
    simpa only [Function.comp_apply,Set.not_infinite] using
      (((G.measurable_infinite_cluster v).comp (measurable_inter_block X)).not).setOf
  exact hf.inter (measurableSet_Iic.preimage
    (measurable_ncard.comp (G.measurable_freshClusterBoundary X v)))

theorem smallFreshBoundary_cost [Countable V] [Countable E]
    (hl : G.LocallyFinite) (p : unitInterval) (X : Set E) (v : V) (M : ℕ)
    (H : Set (Set E)) (hH : MeasurableSet[blockSigma X] H) :
    (1-(p:ℝ))^M * (G.law p).real (H ∩ G.smallFreshBoundary X v M) ≤
      (G.law p).real (H \ G.infiniteEvent v) := by
  let d : Set E → Finset E := fun ω => finiteSetChoice (G.freshClusterBoundary X v ω)
  let A : Finset E → Set (Set E) := fun S => closedBlock ((S : Set E)∩Xᶜ)
  have hd (S : Finset E) : MeasurableSet[blockSigma X] {ω | d ω=S} :=
    @measurableSet_finiteSetChoice (Set E) E (blockSigma X) inferInstance
      (G.freshClusterBoundary X v) (G.measurable_freshClusterBoundary X v) S
  have hA (S : Finset E) : MeasurableSet[blockSigma Xᶜ] (A S) :=
    blockSigma_mono Set.inter_subset_right _
      (measurableSet_closedBlock _ ((S.finite_toSet.subset Set.inter_subset_left).countable))
  have he (ω : Set E) (hω : ω∈G.smallFreshBoundary X v M) :
      ((d ω : Set E)∩Xᶜ)=G.freshClusterBoundary X v ω := by
    change (finiteSetChoice (G.freshClusterBoundary X v ω) : Set E)∩Xᶜ = _
    have hf : (G.freshClusterBoundary X v ω).Finite :=
      (G.finite_cutEdges hl hω.1).subset Set.sdiff_subset
    rw [finiteSetChoice_coe hf]
    exact Set.inter_eq_left.mpr (Set.sdiff_subset_compl _ _)
  have hb (ω : Set E) (hω : ω∈H∩G.smallFreshBoundary X v M) :
      (1-(p:ℝ))^M ≤ (G.law p).real (A (d ω)) := by
    change _ ≤ (G.law p).real (closedBlock ((d ω : Set E)∩Xᶜ))
    rw [he ω hω.2]
    simpa only [law,←law_const,freshClusterBoundary] using law_closedBlock_lower (fun _ : E => p) _
      ((G.finite_cutEdges hl hω.2.1).subset Set.sdiff_subset) p M hω.2.2 (fun _ _ => le_rfl)
  have hh := selected_fresh_lower (fun _ : E => p) X Xᶜ disjoint_compl_right d A hd hA
    (H∩G.smallFreshBoundary X v M) (hH.inter (G.measurableSet_smallFreshBoundary X v M))
    ((1-(p:ℝ))^M) (pow_nonneg (sub_nonneg.mpr p.2.2) _) (by
      simpa only [law,←law_const] using hb)
  simp only [law_const] at hh
  change (1-(p:ℝ))^M * (G.law p).real (H ∩ G.smallFreshBoundary X v M) ≤
    (G.law p).real (H ∩ G.smallFreshBoundary X v M ∩ selectedEvent d A) at hh
  apply hh.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro ω ⟨⟨hωH,hω⟩,hclosed⟩
  refine ⟨hωH,?_⟩
  have hc : Disjoint (G.freshClusterBoundary X v ω) ω := by
    change Disjoint ((d ω : Set E)∩Xᶜ) ω at hclosed
    rwa [he ω hω] at hclosed
  rw [infiniteEvent,Set.mem_ofPred_eq,G.cluster_eq_restricted_of_fresh_closed X v ω hc]
  exact hω.1.not_infinite

end CriticalPercolation.BondGraph
end
end

end OAI
