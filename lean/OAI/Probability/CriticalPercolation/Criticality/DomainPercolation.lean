import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability
import OAI.Probability.CriticalPercolation.Criticality.TwoPoint
import OAI.Probability.CriticalPercolation.Criticality.ContractingDomains
import OAI.Probability.CriticalPercolation.Criticality.DescendingFan
import OAI.Probability.CriticalPercolation.Criticality.IntrinsicCriticalFragility
import OAI.Probability.CriticalPercolation.Criticality.UniformDescendingFan

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def domainInfiniteEvent (S : Set V) (v : V) : Set (Set E) :=
  {ω | (G.cluster (ω∩G.inducedEdges S) v).Infinite}

def domainHitEvent (S : Set V) (x y : V) : Set (Set E) :=
  {ω | y∈G.cluster (ω∩G.inducedEdges S) x}

lemma measurableSet_domainInfiniteEvent [Countable V] [Countable E] (S : Set V) (v : V) :
    MeasurableSet (G.domainInfiniteEvent S v) := by
  exact (G.measurableSet_infiniteEvent v).preimage
    ((BernoulliProduct.measurable_inter_block _).mono (BernoulliProduct.blockSigma_le _) le_rfl)

lemma domainInfiniteEvent_mono {S T : Set V} (hST : S⊆T) (v : V) :
    G.domainInfiniteEvent S v⊆G.domainInfiniteEvent T v := by
  intro ω hω
  exact hω.mono (G.cluster_mono (Set.inter_subset_inter_right _ (show G.inducedEdges S⊆G.inducedEdges T from fun e he x hx => hST (he x hx))) v)

lemma walk_finite_bond_witness {x y : V} (p : G.fullGraph.Walk x y)
    (S : Set V) (hp : ∀ v∈p.support, v∈S) :
    ∃ F : Set E, F.Finite ∧ F⊆G.inducedEdges S ∧ F.ncard≤p.length ∧
      y∈G.cluster F x := by
  induction p with
  | nil => exact ⟨∅,Set.finite_empty,Set.empty_subset _,by simp,.refl _⟩
  | @cons x y z h p ih =>
    obtain ⟨F,hF,hFS,hcard,hconn⟩ := ih (fun v hv => hp v (List.mem_cons_of_mem _ hv))
    obtain ⟨⟨e,_,he⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
    have hex : x∈S := hp x (by simp)
    have hey : y∈S := hp y (List.mem_cons_of_mem _ p.start_mem_support)
    have heS : e∈G.inducedEdges S := by
      intro v hv
      rw [he] at hv
      exact (Sym2.mem_iff.mp hv).elim (fun he => he ▸ hex) (fun he => he ▸ hey)
    refine ⟨insert e F,hF.insert e,Set.insert_subset heS hFS,?_,?_⟩
    · exact (Set.ncard_insert_le e F).trans (by simpa only [SimpleGraph.Walk.length_cons] using Nat.add_le_add_right hcard 1)
    · have hxy : (G.openGraph (insert e F)).Adj x y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_insert _ _,he⟩,hne⟩
      exact hxy.reachable.trans (G.cluster_mono (Set.subset_insert _ _) y hconn)

lemma InsideWalk.domainHit_lower [Countable V] [Countable E]
    (p : unitInterval) {S : Set V} {x y : V} {L : ℕ}
    (h : G.InsideWalk S x y L) :
    (p:ℝ)^L≤(G.law p).real (G.domainHitEvent S x y) := by
  obtain ⟨w,hw,hs⟩ := h
  obtain ⟨F,hF,hFS,hcard,hconn⟩ := G.walk_finite_bond_witness w S hs
  calc
    (p:ℝ)^L ≤ (p:ℝ)^F.ncard := pow_le_pow_of_le_one p.property.1 p.property.2 (hcard.trans hw)
    _ = (G.law p).real {ω : Set E | F⊆ω} := by
      rw [law,←BernoulliProduct.law_const,BernoulliProduct.real_law_subset p F hF]
    _ ≤ (G.law p).real (G.domainHitEvent S x y) := by
      apply measureReal_mono
      · intro ω hω
        exact G.cluster_mono (Set.subset_inter hω hFS) x hconn
      · exact measure_ne_top _ _

lemma domainInfinite_transfer [Countable V] [Countable E]
    (p : unitInterval) (S : Set V) (x y : V) :
    (G.law p).real (G.domainHitEvent S x y) *
        (G.law p).real (G.domainInfiniteEvent S y) ≤
      (G.law p).real (G.domainInfiniteEvent S x) := by
  let H := G.restrictEdges (G.inducedEdges S)
  have he (A : Set (Set (G.inducedEdges S))) (hA : MeasurableSet A) :
      (H.law p).real A = (G.law p).real
        ((fun ω : Set E => (Subtype.val ⁻¹' ω : Set (G.inducedEdges S))) ⁻¹' A) := by
    simp only [measureReal_def]
    congr 1
    rw [←G.law_restrictEdges _ p,Measure.map_apply _ hA]
    exact Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have hh := H.real_infiniteEvent_transfer p x y
  rw [he _ (H.measurableSet_hitEvent _ _),he _ (H.measurableSet_infiniteEvent _),
    he _ (H.measurableSet_infiniteEvent _)] at hh
  simpa only [H,Sharpness.hit_singleton_eq,Set.preimage_ofPred_eq,cluster,domainHitEvent,
    domainInfiniteEvent,infiniteEvent,G.restrictEdges_openGraph,Set.inter_comm,Set.mem_ofPred_eq] using hh

lemma InsideWalk.domainInfinite_lower [Countable V] [Countable E]
    (p : unitInterval) {S : Set V} {x y : V} {L : ℕ}
    (h : G.InsideWalk S x y L) :
    (p:ℝ)^L*(G.law p).real (G.domainInfiniteEvent S y) ≤
      (G.law p).real (G.domainInfiniteEvent S x) :=
  (mul_le_mul_of_nonneg_right (h.domainHit_lower G p) measureReal_nonneg).trans
    (G.domainInfinite_transfer p S x y)

lemma bounded_mass_infinite_subset_domain (v : V) (K : ℝ≥0∞) :
    G.infiniteEvent v\G.massTailEvent v v K ⊆
      G.domainInfiniteEvent (G.weightCeiling v K) v := by
  rintro ω ⟨hi,hm⟩
  change (G.cluster (ω∩G.inducedEdges (G.weightCeiling v K)) v).Infinite
  rw [G.cluster_eq_with_weightCeiling (le_of_not_gt hm)]
  exact hi

lemma real_domainInfinite_ceiling_lower [Countable V] [Countable E]
    (p : unitInterval) (v : V) (K : ℝ≥0∞) :
    (G.law p).real (G.infiniteEvent v)-(G.law p).real (G.massTailEvent v v K) ≤
      (G.law p).real (G.domainInfiniteEvent (G.weightCeiling v K) v) := by
  have he := measureReal_sdiff_add_inter (μ := G.law p) (s := G.infiniteEvent v)
    (G.measurableSet_massTailEvent v v K)
  have hi := measureReal_mono (μ := G.law p)
    (s₁ := G.infiniteEvent v∩G.massTailEvent v v K) Set.inter_subset_right
  have hd := measureReal_mono (μ := G.law p) (G.bounded_mass_infinite_subset_domain v K)
  linarith

theorem uniform_safeDomain_percolation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (o : V) (p : unitInterval)
    (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ R : ℕ, ∃ θ : ℝ, 0<θ ∧ ∀ T : ℝ, ∀ x∈G.safeBallDomain o T R,
      θ≤(G.law p).real (G.domainInfiniteEvent (G.safeBallDomain o T R) x) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hp : 0<(p:ℝ) := by
    by_contra hn
    have he : p=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) p.property.1)
    exact (ne_of_gt hper) (by rw [he,G.law_zero_percolates])
  obtain ⟨θ,hθ,hroot⟩ := G.uniform_rooted_probability hc hl hq p hper
  obtain ⟨K,hK,htail⟩ := G.uniform_massTail_small hq p hm (θ/2) (by positivity)
  obtain ⟨R,C,hC,hlow,hdesc⟩ := G.safeBallDomain_uniform_descent hc hl hq hu o
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hK0 : (0:ℝ)<K := by exact_mod_cast hK
  obtain ⟨L,hL⟩ := hdesc (1/(C*K)) (by positivity)
  refine ⟨R,(p:ℝ)^L*(θ/2),by positivity,?_⟩
  intro T x hx
  obtain ⟨y,hy,hw⟩ := hL T x hx
  have hceil : G.weightCeiling y K⊆G.safeBallDomain o T R := by
    intro z hz
    apply hlow T
    have hzy : G.modularRatio z y≤(K:ℝ) := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ)≤K)).mp
      simpa only [weightCeiling,Set.mem_ofPred_eq,stabilizerWeight,ENNReal.ofReal_natCast] using hz
    change G.modularRatio z o≤T/C
    rw [←G.modularRatio_cocycle hc hl z y o]
    have hypos := (G.modularRatio_pos hc hl y o).le
    have hmul := mul_le_mul_of_nonneg_right hzy hypos
    have hy' : G.modularRatio y o≤T/(C*K) := by simpa only [one_div,inv_mul_eq_div] using hy
    have ht := mul_le_mul_of_nonneg_left hy' hK0.le
    have he : (K:ℝ)*(T/(C*K))=T/C := by field_simp
    exact hmul.trans (he ▸ ht)
  have hm1 := G.real_domainInfinite_ceiling_lower p y K
  have hm2 : θ/2≤(G.law p).real (G.domainInfiniteEvent (G.weightCeiling y K) y) := by
    have hr := hroot y
    have ht := htail y
    linarith
  have hm3 : θ/2≤(G.law p).real (G.domainInfiniteEvent (G.safeBallDomain o T R) y) :=
    hm2.trans (measureReal_mono (G.domainInfiniteEvent_mono hceil y))
  exact (mul_le_mul_of_nonneg_left hm3 (pow_nonneg p.property.1 L)).trans
    (hw.domainInfinite_lower G p)

end CriticalPercolation.BondGraph
end
end

end OAI
