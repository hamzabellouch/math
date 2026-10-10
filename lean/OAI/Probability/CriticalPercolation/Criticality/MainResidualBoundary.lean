import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.GrowthAlternatives
import OAI.Probability.CriticalPercolation.Criticality.SparseLinearCritical
import OAI.Probability.CriticalPercolation.Growth.SuperpolynomialMain
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass
import OAI.Probability.CriticalPercolation.Modular.UnimodularGeometric

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def twoHeavyDistinctEvent (o x y : V) : Set (Set E) :=
  G.heavyClusterEvent o x ∩ G.heavyClusterEvent o y ∩
    {ω | ¬ (G.openGraph ω).Reachable x y}

lemma measurableSet_twoHeavyDistinctEvent [Countable V] [Countable E]
    (o x y : V) : MeasurableSet (G.twoHeavyDistinctEvent o x y) :=
  ((G.measurableSet_heavyClusterEvent o x).inter
    (G.measurableSet_heavyClusterEvent o y)).inter (G.measurable_reachable x y).not.setOf

lemma atMostOneInfinite_ae_of_no_light_or_two_heavy
    [Countable V] [Countable E] (p : unitInterval) (o : V)
    (hl : ∀ v, G.law p (G.lightInfiniteEvent o v) = 0)
    (hh : ∀ x y, G.law p (G.twoHeavyDistinctEvent o x y) = 0) :
    ∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite := by
  have hla : ∀ᵐ ω ∂G.law p, ∀ v, ω ∉ G.lightInfiniteEvent o v := by
    apply ae_all_iff.mpr
    intro v
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hl v
  have hha : ∀ᵐ ω ∂G.law p, ∀ x y, ω ∉ G.twoHeavyDistinctEvent o x y := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hh x y
  filter_upwards [hla,hha] with ω hωl hωh
  intro x y hx hy
  have hheavy (v : V) (hv : (G.cluster ω v).Infinite) :
      ω ∈ G.heavyClusterEvent o v := by
    have hm : ω ∈ G.infiniteEvent v := hv
    rw [G.infiniteEvent_eq_light_union_heavy o v] at hm
    exact hm.resolve_left (hωl v)
  by_contra hxy
  exact hωh x y ⟨⟨hheavy x hx,hheavy y hy⟩,hxy⟩

lemma positive_light_or_two_heavy_of_exponential_critical_percolation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ))
    (hper : G.law G.criticalProbability G.percolates ≠ 0) :
    (∃ v, 0 < G.law G.criticalProbability (G.lightInfiniteEvent o v)) ∨
      ∃ x y, 0 < G.law G.criticalProbability (G.twoHeavyDistinctEvent o x y) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_contra h
  push Not at h
  have hln : ∀ v, G.law G.criticalProbability (G.lightInfiniteEvent o v) = 0 :=
    fun v => le_antisymm (h.1 v) bot_le
  have hhn : ∀ x y, G.law G.criticalProbability (G.twoHeavyDistinctEvent o x y) = 0 :=
    fun x y => le_antisymm (h.2 x y) bot_le
  exact hper (Sharpness.critical_null_of_unique G hc hl hq o γ hγ N hgrowth
    (G.atMostOneInfinite_ae_of_no_light_or_two_heavy G.criticalProbability o hln hhn))

theorem main_residual_boundary [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability < 1) (o : V)
    (hper : G.law G.criticalProbability G.percolates ≠ 0) :
    (¬ G.CombinatoriallyUnimodular ∧
      ((∃ v, 0 < G.law G.criticalProbability (G.lightInfiniteEvent o v)) ∨
        ∃ x y, 0 < G.law G.criticalProbability (G.twoHeavyDistinctEvent o x y))) ∨
    (G.SubexponentialGrowth ∧ ∃ d : ℕ, 2 ≤ d ∧
      ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard ≤ n^d) := by
  rcases G.growth_alternative hc hl hq with hg | ⟨γ,hγ,N,hgrowth⟩
  · rcases G.superpolynomial_or_polynomial_scales with hsp | ⟨d,hd⟩
    · exact False.elim (hper (G.no_percolation_at_criticality_superpolynomial hc hl hq hpc hg hsp))
    · right
      refine ⟨hg,d,?_,hd⟩
      by_contra hsmall
      have hd1 : d ≤ 1 := by omega
      have hlin : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard ≤ 1*n := by
        intro R
        obtain ⟨n,hn,v,hv⟩ := hd (max R 1)
        refine ⟨n,le_trans (le_max_left _ _) hn,v,hv.trans ?_⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd1 with rfl|rfl
        · simp only [pow_zero,one_mul]
          exact le_trans (le_max_right _ _) hn
        · simp
      have he := G.moving_sparse_linear_critical_one hc hl hq 1 hlin
      rw [he] at hpc
      exact (lt_irrefl _ hpc)
  · left
    refine ⟨?_,G.positive_light_or_two_heavy_of_exponential_critical_percolation
      hc hl hq o γ hγ N hgrowth hper⟩
    intro hu
    exact hper (CombinatoriallyUnimodular.exponential_critical_null G hu hc hl hq hpc
      o γ hγ N hgrowth)

end CriticalPercolation.BondGraph
end
end

end OAI
