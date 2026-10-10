import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteOpenWitness
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass
import OAI.Probability.CriticalPercolation.Criticality.DescendingFan
import OAI.Probability.CriticalPercolation.GraphGeometry.InfiniteEventSubsetHit
import OAI.Probability.CriticalPercolation.Modular.CriticalHeavyNull
import OAI.Probability.CriticalPercolation.Modular.HeavyHarris

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.massTailEvent_preimage (φ : G.Aut) (v : V) (K : ℝ≥0∞) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.massTailEvent (φ.vertex v) (φ.vertex v) K=
      G.massTailEvent v v K := by
  ext ω
  change K<G.modularMass (φ.vertex v) (G.cluster (φ.edge '' ω) (φ.vertex v)) ↔ _
  rw [←φ.cluster_image,φ.modularMass_image]
  rfl

lemma Aut.massTailEvent_real [Countable V] [Countable E] (φ : G.Aut)
    (p : unitInterval) (v : V) (K : ℝ≥0∞) :
    (G.law p).real (G.massTailEvent (φ.vertex v) (φ.vertex v) K)=
      (G.law p).real (G.massTailEvent v v K) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_massTailEvent _ _ _),φ.massTailEvent_preimage]

lemma uniform_massTail_small [Countable V] [Countable E]
    (hq : G.QuasiTransitive) (p : unitInterval)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞)
    (η : ℝ) (hη : 0<η) :
    ∃ K : ℕ, 1≤K ∧ ∀ v, (G.law p).real (G.massTailEvent v v K)<η := by
  have hz (v : V) : (G.law p).real (G.heavyClusterEvent v v)=0 := by
    have hn : G.law p (G.heavyClusterEvent v v)=0 := by
      simpa only [heavyClusterEvent,not_not] using ae_iff.mp (hm v)
    simp only [measureReal_def,hn,ENNReal.toReal_zero]
  obtain ⟨S,hS,hcover⟩ := hq
  have he (v : V) : ∀ᶠ K : ℕ in atTop, (G.law p).real (G.massTailEvent v v K)<η := by
    have h := G.tendsto_real_massTail p v v
    rw [hz] at h
    exact h.eventually (gt_mem_nhds hη)
  obtain ⟨K,hK,hall⟩ := ((eventually_ge_atTop 1).and
    (hS.toFinset.eventually_all.mpr (fun v _ => he v))).exists
  refine ⟨K,hK,fun v => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover v
  rw [φ.massTailEvent_real]
  exact hall s (hS.mem_toFinset.mpr hs)

lemma real_descendingFan_lower [Countable V] [Countable E]
    (p : unitInterval) (v : V) (K ε : ℝ≥0∞) (hK : K≠∞) (hε : 0<ε) (N : ℕ) :
    (G.law p).real (G.infiniteEvent v) - (G.law p).real (G.massTailEvent v v K) ≤
      (G.law p).real (G.descendingFanEvent v K ε N) := by
  have he := measureReal_sdiff_add_inter (μ := G.law p) (s := G.infiniteEvent v)
    (G.measurableSet_massTailEvent v v K)
  have hi : (G.law p).real (G.infiniteEvent v ∩ G.massTailEvent v v K) ≤
      (G.law p).real (G.massTailEvent v v K) :=
    measureReal_mono Set.inter_subset_right
  have hd : (G.law p).real (G.infiniteEvent v \ G.massTailEvent v v K) ≤
      (G.law p).real (G.descendingFanEvent v K ε N) :=
    measureReal_mono (G.bounded_mass_infinite_subset_fan v K ε hK hε N)
  linarith

theorem uniform_descendingFans_of_light_percolation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ θ : ℝ, 0<θ ∧ ∃ K : ℕ, 1≤K ∧ ∀ ε : ℝ≥0∞, 0<ε → ∀ N : ℕ, ∀ v : V,
      θ < (G.law p).real (G.descendingFanEvent v K ε N) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨θ,hθ,hroot⟩ := G.uniform_rooted_probability hc hl hq p hper
  obtain ⟨K,hK,htail⟩ := G.uniform_massTail_small hq p hm (θ/4) (by positivity)
  refine ⟨θ/2,by positivity,K,hK,fun ε hε N v => ?_⟩
  have h := G.real_descendingFan_lower p v K ε (ENNReal.natCast_ne_top K) hε N
  have hr := hroot v
  have ht := htail v
  linarith

lemma lower_uniform_descendingFan [Countable E]
    (hq : G.QuasiTransitive) (p : unitInterval) (hp : 0<p)
    (K ε : ℝ≥0∞) (N : ℕ) (θ : ℝ)
    (hfan : ∀ v : V, θ < (G.law p).real (G.descendingFanEvent v K ε N)) :
    ∃ q : unitInterval, (p : ℝ)/2≤q ∧ q<p ∧
      ∀ v : V, θ<(G.law q).real (G.descendingFanEvent v K ε N) := by
  obtain ⟨S,hS,hcover⟩ := hq
  let : Finite S := hS.to_subtype
  obtain ⟨q,hhalf,hqp,hall⟩ := BernoulliProduct.exists_lower_parameter
    (fun s : S => G.descendingFanEvent s K ε N)
    (fun s => G.descendingFanEvent_upper s K ε N)
    (fun s => G.descendingFanEvent_finiteWitness s K ε N) p hp
    (fun _ => θ) (fun s => by simpa only [BernoulliProduct.law_const,BondGraph.law] using hfan s)
  refine ⟨q,hhalf,hqp,fun v => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover v
  rw [φ.descendingFanEvent_real]
  simpa only [BernoulliProduct.law_const,BondGraph.law] using hall ⟨s,hs⟩

theorem counterexample_descending_fans_subcritical
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    ∃ θ : ℝ, 0<θ ∧ ∃ K : ℕ, 1≤K ∧ ∀ ε : ℝ≥0∞, 0<ε → ∀ N : ℕ,
      ∃ q : unitInterval, (G.criticalProbability : ℝ)/2≤q ∧ q<G.criticalProbability ∧
        ∀ v : V, θ<(G.law q).real (G.descendingFanEvent v K ε N) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  have hp : 0<G.criticalProbability := by
    by_contra hn
    have he : G.criticalProbability=0 := le_antisymm (le_of_not_gt hn) bot_le
    exact hper (by rw [he,G.law_zero_percolates])
  obtain ⟨θ,hθ,K,hK,hfan⟩ := G.uniform_descendingFans_of_light_percolation hc hl hq
    G.criticalProbability (pos_iff_ne_zero.mpr hper) (fun v =>
      (G.nonunimodular_critical_mass_finite_ae hc hl hq hpc hu v).mono (fun ω h => (h v).ne))
  refine ⟨θ,hθ,K,hK,fun ε hε N => ?_⟩
  exact G.lower_uniform_descendingFan hq G.criticalProbability hp K ε N θ (hfan ε hε N)

end CriticalPercolation.BondGraph
end
end

end OAI
