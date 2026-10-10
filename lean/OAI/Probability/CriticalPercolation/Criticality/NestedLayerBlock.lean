import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.DescendingFan
import OAI.Probability.CriticalPercolation.Criticality.UniformDescendingFan
import OAI.Probability.CriticalPercolation.Gluing.DomainFreshExit
import OAI.Probability.CriticalPercolation.GraphGeometry.NestedLayerGeometry

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def boundedDomainFreshExitEvent (D S : Set V) (v : V) (N : ℕ) (M : ℝ≥0∞) : Set (Set E) :=
  G.domainFreshExitEvent D S v N ∩
    {ω | G.modularMass v (G.cluster ((ω∩G.inducedEdges D)∩G.inducedEdges S) v)≤M}

lemma boundedDomainFreshExit_of_full_mass (D S : Set V) (v : V) (N : ℕ) (M : ℝ≥0∞) :
    G.domainFreshExitEvent D S v N\G.massTailEvent v v M ⊆
      G.boundedDomainFreshExitEvent D S v N M := by
  intro ω hω
  exact ⟨hω.1,(G.modularMass_mono v (G.cluster_mono
    (Set.inter_subset_left.trans Set.inter_subset_left) v)).trans (le_of_not_gt hω.2)⟩

lemma real_boundedDomainFreshExit_lower [Countable V] [Countable E]
    (p : unitInterval) (D S : Set V) (v : V) (N : ℕ) (M : ℝ≥0∞) :
    (G.law p).real (G.domainFreshExitEvent D S v N)-
      (G.law p).real (G.massTailEvent v v M) ≤
      (G.law p).real (G.boundedDomainFreshExitEvent D S v N M) := by
  have he := measureReal_sdiff_add_inter (μ := G.law p)
    (s := G.domainFreshExitEvent D S v N) (G.measurableSet_massTailEvent v v M)
  have hi := measureReal_mono (μ := G.law p)
    (s₁ := G.domainFreshExitEvent D S v N ∩ G.massTailEvent v v M) Set.inter_subset_right
  have hd := measureReal_mono (μ := G.law p) (G.boundedDomainFreshExit_of_full_mass D S v N M)
  linarith

theorem uniform_nestedLayer_blocks
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (o : V)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ R : ℕ, ∃ θ : ℝ, 0<θ ∧ ∃ M : ℕ, 1≤M ∧ ∀ a : ℝ, 0<a → ∀ N : ℕ,
      ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ δ<a ∧ ∀ T : ℝ, 0<T → ∀ x∈G.safeBallDomain o T R,
        a*T≤G.modularRatio x o →
        θ<(G.law p).real (G.boundedDomainFreshExitEvent
          (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N M) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨θ,hθ,K,hK,hfront⟩ := G.uniform_domainFreshExit_of_mass hc hl hq p hp hp1 hper hm
  obtain ⟨R,C,hC,hlow,hdesc⟩ := G.safeBallDomain_uniform_descent hc hl hq hu o
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hK0 : (0:ℝ)<K := by exact_mod_cast hK
  obtain ⟨L,hL⟩ := hdesc (1/(C*K)) (by positivity)
  let α : ℝ := (p:ℝ)^L*θ
  have hα : 0<α := mul_pos (pow_pos hp L) hθ
  obtain ⟨M,hM,htail⟩ := G.uniform_massTail_small hq p hm (α/4) (by positivity)
  refine ⟨R,α/2,by positivity,M,hM,fun a ha N => ?_⟩
  obtain ⟨H,hH⟩ := hfront N
  obtain ⟨δ,hδ,hδ1,hδa,hgap⟩ := G.exists_layer_gap hc hl hq o a ha L H R
  refine ⟨δ,hδ,hδ1,hδa,fun T hT x hx hband => ?_⟩
  obtain ⟨y,hy,hw⟩ := hL T x hx
  have hceil : G.weightCeiling y K⊆G.safeBallDomain o T R := by
    intro z hz
    apply hlow T
    have hzy : G.modularRatio z y≤(K:ℝ) := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ)≤K)).mp
      simpa only [weightCeiling,Set.mem_ofPred_eq,stabilizerWeight,ENNReal.ofReal_natCast] using hz
    change G.modularRatio z o≤T/C
    rw [←G.modularRatio_cocycle hc hl z y o]
    have hmul := mul_le_mul_of_nonneg_right hzy (G.modularRatio_pos hc hl y o).le
    have hy' : G.modularRatio y o≤T/(C*K) := by simpa only [one_div,inv_mul_eq_div] using hy
    have ht := mul_le_mul_of_nonneg_left hy' hK0.le
    have he : (K:ℝ)*(T/(C*K))=T/C := by field_simp
    exact hmul.trans (he ▸ ht)
  obtain ⟨w,hlen,hsupport⟩ := hw
  have hyball : y∈G.vertexBall x L := G.vertexBall_mono x hlen (G.walk_mem_vertexBall w)
  have hxb : x∉G.safeBallDomain o (δ*T) R := (hgap T hT x hband).1 x (G.mem_vertexBall_self x L)
  have hyb : y∉G.safeBallDomain o (δ*T) R := (hgap T hT x hband).1 y hyball
  have hw' : G.InsideWalk ((G.safeBallDomain o T R)∩(G.safeBallDomain o (δ*T) R)ᶜ) x y L := by
    refine ⟨w,hlen,fun z hz => ⟨hsupport z hz,?_⟩⟩
    exact (hgap T hT x hband).1 z (G.walk_support_mem_start_ball w hlen hz)
  have hf : ∀ᵐ ω ∂G.law p,
      (G.cluster (ω∩G.inducedEdges (G.safeBallDomain o (δ*T) R)ᶜ) y).Finite := by
    filter_upwards [hm y] with ω hω
    exact G.finite_cluster_outside_safe hc hl hq o (δ*T) (mul_pos hδ hT) R y hyb ω hω
  have hsuccess := hH (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ y
    hceil ((hgap T hT x hband).2 y hyball) hf
  have htrans := hw'.domainFreshExit_transfer G p hxb hyb N
  have hxsuccess : α<(G.law p).real (G.domainFreshExitEvent
      (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N) :=
    (mul_lt_mul_of_pos_left hsuccess (pow_pos hp L)).trans_le htrans
  have hbound := G.real_boundedDomainFreshExit_lower p (G.safeBallDomain o T R)
    (G.safeBallDomain o (δ*T) R)ᶜ x N M
  have ht := htail x
  linarith

end CriticalPercolation.BondGraph
end
end

end OAI
