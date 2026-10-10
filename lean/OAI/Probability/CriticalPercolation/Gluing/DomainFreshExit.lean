import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import OAI.Probability.CriticalPercolation.Exploration.SliceExploration
import OAI.Probability.CriticalPercolation.Criticality.ContractingDomains
import OAI.Probability.CriticalPercolation.Criticality.DomainPercolation
import OAI.Probability.CriticalPercolation.Gluing.FreshExitContinuity
import OAI.Probability.CriticalPercolation.Gluing.FreshExitWitness
import OAI.Probability.CriticalPercolation.Gluing.UniformFreshBoundary
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

def domainFreshExitEvent (D S : Set V) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | ω∩G.inducedEdges D ∈ G.freshExitEvent S v N}

lemma domainFreshExitEvent_upper {D S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    IsUpperSet (G.domainFreshExitEvent D S v N) :=
  (G.freshExitEvent_upper hv N).preimage (fun _ _ h => Set.inter_subset_inter_left _ h)

lemma domainFreshExitEvent_finiteWitness {D S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    HasFiniteOpenWitness (G.domainFreshExitEvent D S v N) := by
  intro ω hω
  obtain ⟨F,hF,hFω,hFe⟩ := G.freshExitEvent_finiteWitness hv N _ hω
  refine ⟨F,hF,hFω.trans Set.inter_subset_left,?_⟩
  change F∩G.inducedEdges D ∈ G.freshExitEvent S v N
  rwa [Set.inter_eq_left.mpr (hFω.trans Set.inter_subset_right)]

lemma measurableSet_domainFreshExitEvent [Countable E]
    {D S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    MeasurableSet (G.domainFreshExitEvent D S v N) :=
  measurableSet_finiteWitness _ (G.domainFreshExitEvent_upper hv N)
    (G.domainFreshExitEvent_finiteWitness hv N)

lemma freshExit_in_domain_of_mass (D S : Set V) (v : V) (K : ℝ≥0∞) (N : ℕ)
    (hD : G.weightCeiling v K⊆D) :
    G.freshExitEvent S v N\G.massTailEvent v v K ⊆ G.domainFreshExitEvent D S v N := by
  rintro ω ⟨⟨F,hF,hFω⟩,hm⟩
  have hmass : G.modularMass v (G.cluster ω v)≤K := le_of_not_gt hm
  let X := G.inducedEdges S
  let C := G.inducedEdges (G.weightCeiling v K)
  have hCD : C⊆G.inducedEdges D := G.inducedEdges_monotone hD
  have hC : G.cluster ((ω∩G.inducedEdges D)∩X) v=G.cluster (ω∩X) v := by
    apply Set.Subset.antisymm (G.cluster_mono (Set.inter_subset_inter_left _ Set.inter_subset_left) v)
    have he : G.cluster ((ω∩X)∩C) v=G.cluster (ω∩X) v :=
      G.cluster_eq_with_weightCeiling
        ((G.modularMass_mono v (G.cluster_mono Set.inter_subset_left v)).trans hmass)
    rw [←he]
    apply G.cluster_mono
    intro e he
    exact ⟨⟨he.1.1,hCD he.2⟩,he.1.2⟩
  refine ⟨F,hF,fun e he => ?_⟩
  obtain ⟨⟨x,y,hexy,hx,hy⟩,heX⟩ := (hFω he).1
  have hyC : y∈G.cluster ω v := G.cluster_mono Set.inter_subset_left v hy
  have hxC : x∈G.cluster ω v := by
    by_cases heq : y=x
    · simpa only [heq] using hyC
    · exact hyC.trans (show (G.openGraph ω).Adj y x from by
        apply (SimpleGraph.fromEdgeSet_adj _).mpr
        refine ⟨⟨e,(hFω he).2,?_⟩,heq⟩
        rw [hexy,Sym2.eq_swap]).reachable
  have heD : e∈G.inducedEdges D := by
    apply hCD
    intro z hz
    rw [hexy] at hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact (G.stabilizerWeight_le_modularMass hxC).trans hmass
    · exact (G.stabilizerWeight_le_modularMass hyC).trans hmass
  refine ⟨⟨⟨x,y,hexy,?_,?_⟩,heX⟩,(hFω he).2,heD⟩
  · change x∉G.cluster ((ω∩G.inducedEdges D)∩X) v
    rwa [hC]
  · change y∈G.cluster ((ω∩G.inducedEdges D)∩X) v
    rwa [hC]

lemma freshExit_same_cluster {S : Set V} {x y : V} {N : ℕ} {ω : Set E}
    (hxy : y∈G.cluster (ω∩G.inducedEdges S) x) :
    ω∈G.freshExitEvent S x N ↔ ω∈G.freshExitEvent S y N := by
  simp only [freshExitEvent,Set.mem_ofPred_eq,freshClusterBoundary]
  rw [G.cluster_eq_of_reachable hxy]

lemma InsideWalk.domainFreshExit_transfer [Countable V] [Countable E]
    (p : unitInterval) {D S : Set V} {x y : V} {L : ℕ} (_ : x∈S) (hy : y∈S)
    (h : G.InsideWalk (D∩S) x y L) (N : ℕ) :
    (p:ℝ)^L*(G.law p).real (G.domainFreshExitEvent D S y N) ≤
      (G.law p).real (G.domainFreshExitEvent D S x N) := by
  obtain ⟨w,hw,hs⟩ := h
  obtain ⟨F,hF,hFS,hcard,hconn⟩ := G.walk_finite_bond_witness w (D∩S) hs
  let A : Set (Set E) := {ω | F⊆ω}
  have hA : IsUpperSet A := fun _ _ hωη hω => hω.trans hωη
  have hAw : HasFiniteOpenWitness A := fun ω hω => ⟨F,hF,hω,Set.Subset.rfl⟩
  have hH := harris_finiteWitness (fun _ : E => p) A (G.domainFreshExitEvent D S y N)
    hA (G.domainFreshExitEvent_upper hy N) hAw (G.domainFreshExitEvent_finiteWitness hy N)
  simp only [law_const] at hH
  have hsub : A∩G.domainFreshExitEvent D S y N ⊆ G.domainFreshExitEvent D S x N := by
    intro ω hω
    apply (G.freshExit_same_cluster (S := S) (x := x) (y := y) (N := N) (ω := ω∩G.inducedEdges D) ?_).mpr hω.2
    apply G.cluster_mono (ω := F) _ x hconn
    intro e he
    refine ⟨⟨hω.1 he,fun z hz => (hFS he z hz).1⟩,fun z hz => (hFS he z hz).2⟩
  have hprob : (p:ℝ)^L≤(G.law p).real A := by
    rw [law,←law_const,real_law_subset p F hF]
    exact pow_le_pow_of_le_one p.2.1 p.2.2 (hcard.trans hw)
  exact (mul_le_mul_of_nonneg_right hprob measureReal_nonneg).trans
    (hH.trans (measureReal_mono hsub))

theorem uniform_domainFreshExit_of_mass
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ θ : ℝ, 0<θ ∧ ∃ K : ℕ, 1≤K ∧ ∀ N : ℕ, ∃ R : ℕ,
      ∀ (D S : Set V) (v : V), G.weightCeiling v K⊆D → G.vertexBall v R⊆S →
      (∀ᵐ ω ∂G.law p, (G.cluster (ω∩G.inducedEdges S) v).Finite) →
      θ<(G.law p).real (G.domainFreshExitEvent D S v N) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨θ,hθ,hroot⟩ := G.uniform_rooted_probability hc hl hq p hper
  obtain ⟨K,hK,htail⟩ := G.uniform_massTail_small hq p hm (θ/4) (by positivity)
  refine ⟨θ/2,by positivity,K,hK,fun N => ?_⟩
  obtain ⟨R,hR⟩ := G.fewOpenFreshBoundary_uniform_ball hc hl hq p hp hp1 N (θ/4) (by positivity)
  refine ⟨R,fun D S v hD hS hf => ?_⟩
  have hfail : (G.law p).real (G.infiniteEvent v\G.freshExitEvent S v N)<θ/4 := by
    exact lt_of_le_of_lt
      (ENNReal.toReal_mono (measure_ne_top _ _)
        (G.infinite_sdiff_freshExit_bound hl p S v N hf))
      (hR v _ (G.inducedEdges_monotone hS))
  have hcover : G.infiniteEvent v⊆
      (G.infiniteEvent v\G.freshExitEvent S v N)∪
        (G.massTailEvent v v K∪G.domainFreshExitEvent D S v N) := by
    intro ω hω
    by_cases he : ω∈G.freshExitEvent S v N
    · right
      by_cases hm : ω∈G.massTailEvent v v K
      · exact Or.inl hm
      · exact Or.inr (G.freshExit_in_domain_of_mass D S v K N hD ⟨he,hm⟩)
    · exact Or.inl ⟨hω,he⟩
  have hprob := (measureReal_mono hcover (μ := G.law p)).trans (measureReal_union_le _ _)
  have hu := measureReal_union_le (G.massTailEvent v v K) (G.domainFreshExitEvent D S v N) (μ := G.law p)
  have hr := hroot v
  have ht := htail v
  linarith

end CriticalPercolation.BondGraph
end
end

end OAI
