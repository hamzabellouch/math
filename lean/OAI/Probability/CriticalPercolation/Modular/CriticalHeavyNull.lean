import Mathlib
import OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
import OAI.Probability.CriticalPercolation.Criticality.SubcriticalLocalRateBound
import OAI.Probability.CriticalPercolation.Modular.ClusterDiscrepancy
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyUniqueness
import OAI.Probability.CriticalPercolation.Modular.HeavyHarris
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass
import OAI.Probability.CriticalPercolation.Modular.ModularGrowth

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.heavyClusterEvent_iff (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (o v : V) (ω : Set E) :
    φ.edge '' ω∈G.heavyClusterEvent o (φ.vertex v) ↔ ω∈G.heavyClusterEvent o v := by
  change G.modularMass o (G.cluster _ _)=∞ ↔ _
  rw [G.modularMass_eq_top_change_base hc hl o (φ.vertex o),←φ.cluster_image,φ.modularMass_image]
  rfl

lemma Aut.heavyClusterEvent_measure [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (p : unitInterval) (o v : V) :
    G.law p (G.heavyClusterEvent o (φ.vertex v))=G.law p (G.heavyClusterEvent o v) := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_heavyClusterEvent _ _)]
  congr 1
  ext ω
  exact φ.heavyClusterEvent_iff G hc hl o v ω

lemma heavyClusterEvent_pos_all [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : 0<p) (o v : V)
    (hv : 0<G.law p (G.heavyClusterEvent o v)) (x : V) :
    0<G.law p (G.heavyClusterEvent o x) := by
  by_contra hn
  have hz : G.law p (G.heavyClusterEvent o x)=0 := le_antisymm (le_of_not_gt hn) bot_le
  obtain ⟨S,hS,_,hSv⟩ := G.mem_cluster_finite_witness (hc x v)
  have hnull := BernoulliProduct.finite_union_preimage_null (fun _ : E => p)
    (fun _ => hp) S hS (G.heavyClusterEvent o x) (G.measurableSet_heavyClusterEvent _ _) (by
      rwa [BernoulliProduct.law_const])
  rw [BernoulliProduct.law_const] at hnull
  have hle : G.law p (G.heavyClusterEvent o v)≤0 := by
    rw [←hnull]
    apply measure_mono
    intro ω hω
    change G.modularMass o (G.cluster (S∪ω) x)=∞
    have hr := G.cluster_mono (Set.subset_union_left : S⊆S∪ω) x hSv
    rw [G.cluster_eq_of_reachable hr]
    exact top_unique (hω ▸ G.modularMass_mono o (G.cluster_mono Set.subset_union_right v))
  exact (not_lt_of_ge hle) hv

lemma uniform_heavy_probability [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : 0<p) (o v : V) (hv : 0<G.law p (G.heavyClusterEvent o v)) :
    ∃ θ : ℝ, 0<θ ∧ ∀ x, θ≤(G.law p).real (G.heavyClusterEvent o x) := by
  have hall (x : V) : 0<(G.law p).real (G.heavyClusterEvent o x) :=
    ENNReal.toReal_pos (G.heavyClusterEvent_pos_all hc p hp o v hv x).ne' (measure_ne_top _ _)
  obtain ⟨S,hS,hcover⟩ := hq
  have hne : S.Nonempty := by
    obtain ⟨s,hs,_⟩ := hcover v
    exact ⟨s,hs⟩
  obtain ⟨s,hs,hmin⟩ := Set.exists_min_image S
    (fun x => (G.law p).real (G.heavyClusterEvent o x)) hS hne
  refine ⟨(G.law p).real (G.heavyClusterEvent o s),hall s,?_⟩
  intro x
  obtain ⟨t,ht,φ,rfl⟩ := hcover x
  simp only [measureReal_def,φ.heavyClusterEvent_measure G hc hl]
  exact hmin t ht

lemma uniqueHeavy_twoPoint_lower [Countable V] [Countable E] (p : unitInterval)
    (o : V) (hu : ∀ᵐ ω ∂G.law p, ω∈G.atMostOneHeavy o) (x y : V) :
    (G.law p).real (G.heavyClusterEvent o x) * (G.law p).real (G.heavyClusterEvent o y) ≤
      CriticalPercolation.Sharpness.twoPoint G p x y := by
  apply (G.harris_heavyClusterEvent p o x y).trans
  unfold CriticalPercolation.Sharpness.twoPoint
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hu] with ω hω
  intro h
  rw [CriticalPercolation.Sharpness.hit_singleton_eq]
  exact hω x y h.1 h.2

theorem exponential_critical_heavy_null
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (o v : V)
    (γ : ℝ) (hγ : 0<γ) (N : ℕ)
    (hgrowth : ∀ n≥N, ∀ x : V, γ*n≤Real.log ((G.vertexBall x n).ncard : ℝ)) :
    G.law G.criticalProbability (G.heavyClusterEvent o v)=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_contra hn
  have hv : 0<G.law G.criticalProbability (G.heavyClusterEvent o v) := bot_lt_iff_ne_bot.mpr hn
  have hp : 0<G.criticalProbability := by
    by_contra hh
    have he : G.criticalProbability=0 := le_antisymm (le_of_not_gt hh) bot_le
    have hsub : G.heavyClusterEvent o v⊆G.percolates :=
      fun ω hω => ⟨v,G.infinite_of_modularMass_top o hω⟩
    have hn' := (measure_mono (μ := G.law G.criticalProbability) hsub)
    rw [he,G.law_zero_percolates] at hn'
    rw [he] at hv
    exact (not_lt_of_ge hn') hv
  obtain ⟨θ,hθ,hall⟩ := G.uniform_heavy_probability hc hl hq G.criticalProbability hp o v hv
  apply CriticalPercolation.Sharpness.no_uniform_critical_twoPoint G hl hq hp o γ hγ N hgrowth
  refine ⟨θ*θ,mul_pos hθ hθ,?_⟩
  intro x y
  exact (mul_le_mul (hall x) (hall y) hθ.le measureReal_nonneg).trans
    (G.uniqueHeavy_twoPoint_lower G.criticalProbability o
      (G.atMostOneHeavy_critical_ae hc hl hq hpc o) x y)

theorem nonunimodular_critical_mass_finite_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ∀ v, G.modularMass o (G.cluster ω v)<∞ := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  let : Nonempty V := ⟨o⟩
  obtain ⟨γ,hγ,N,hgrowth⟩ := G.exponential_of_not_combinatoriallyUnimodular hc hl hq hu
  apply ae_all_iff.mpr
  intro v
  have hn := G.exponential_critical_heavy_null hc hl hq hpc o v γ hγ N hgrowth
  rw [ae_iff]
  simpa only [lt_top_iff_ne_top,not_not,heavyClusterEvent] using hn

end CriticalPercolation.BondGraph
end
end

end OAI
