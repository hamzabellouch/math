import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infiniteEvent_subset_hit_compl (o : V) (K : Set V) (hK : K.Finite) :
    G.infiniteEvent o ⊆ G.hitEvent o Kᶜ := by
  intro ω hω
  exact (hω.sdiff hK).nonempty

lemma infiniteEvent_eq_iInter_hit_compl
    (K : Set.FiniteExhaustion (Set.univ : Set V)) (o : V) :
    G.infiniteEvent o = ⋂ n, G.hitEvent o (K n)ᶜ := by
  ext ω
  constructor
  · intro hω
    exact Set.mem_iInter.mpr fun n => G.infiniteEvent_subset_hit_compl o (K n) (K.finite n) hω
  · intro hω
    change (G.cluster ω o).Infinite
    intro hfin
    obtain ⟨n, hn⟩ := finite_subset_exhaustion K hfin (Set.subset_univ _)
    obtain ⟨v, hv, hvK⟩ := Set.mem_iInter.mp hω n
    exact hvK (hn hv)

lemma tendsto_real_hit_compl [Countable V] [Countable E]
    (p : unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set V)) (o : V) :
    Tendsto (fun n => (G.law p).real (G.hitEvent o (K n)ᶜ)) atTop
      (𝓝 ((G.law p).real (G.infiniteEvent o))) := by
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (G.measurableSet_hitEvent o (K n)ᶜ).nullMeasurableSet)
    (show Antitone (fun n => G.hitEvent o (K n)ᶜ) from
      fun _ _ h => G.hitEvent_mono_target o (Set.compl_subset_compl.mpr (K.mono h)))
    ⟨0, measure_ne_top _ _⟩
  rw [← G.infiniteEvent_eq_iInter_hit_compl K o] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma real_hit_singleton_pos (hconnected : G.fullGraph.Connected)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (o v : V) :
    0 < (G.law p).real (G.hitEvent o {v}) := by
  obtain ⟨s, hs, _, hsv⟩ := G.mem_cluster_finite_witness (hconnected o v)
  have hsub : {ω : Set E | s ⊆ ω} ⊆ G.hitEvent o {v} := by
    intro ω hω
    exact ⟨v, G.cluster_mono hω o hsv, rfl⟩
  have hpos : 0 < (G.law p).real {ω : Set E | s ⊆ ω} := by
    rw [law, ← BernoulliProduct.law_const (E := E) p]
    rw [BernoulliProduct.real_law_subset p s hs]
    exact pow_pos hp _
  exact lt_of_lt_of_le hpos (measureReal_mono hsub)

lemma real_infiniteEvent_transfer [Countable V] [Countable E]
    (p : unitInterval) (o v : V) :
    (G.law p).real (G.hitEvent o {v}) * (G.law p).real (G.infiniteEvent v) ≤
      (G.law p).real (G.infiniteEvent o) := by
  let K := (Set.to_countable (Set.univ : Set V)).finiteExhaustion
  have hn (n : ℕ) :
      (G.law p).real (G.hitEvent o {v}) * (G.law p).real (G.infiniteEvent v) ≤
        (G.law p).real (G.hitEvent o (K n)ᶜ) := by
    apply le_trans (G.joint_gluing p o {v} (K n)ᶜ
      ((G.law p).real (G.infiniteEvent v)) ?_)
      (measureReal_mono Set.inter_subset_right)
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact measureReal_mono (G.infiniteEvent_subset_hit_compl w (K n) (K.finite n))
  exact ge_of_tendsto (G.tendsto_real_hit_compl p K o) (Eventually.of_forall hn)

lemma real_infiniteEvent_pos_all [Countable V] [Countable E]
    (hconnected : G.fullGraph.Connected) (p : unitInterval) (hp : 0 < (p : ℝ))
    {v : V} (hv : 0 < (G.law p).real (G.infiniteEvent v)) (o : V) :
    0 < (G.law p).real (G.infiniteEvent o) :=
  lt_of_lt_of_le (mul_pos (G.real_hit_singleton_pos hconnected p hp o v) hv)
    (G.real_infiniteEvent_transfer p o v)

theorem uniform_rooted_probability
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (p : unitInterval)
    (hp : 0 < G.law p G.percolates) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ o : V, θ ≤ (G.law p).real (G.infiniteEvent o) := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  have hp0 : 0 < (p : ℝ) := by
    by_contra h
    have hz : p = 0 := Subtype.ext (le_antisymm (not_lt.mp h) p.property.1)
    subst p
    rw [G.law_zero_percolates] at hp
    exact (lt_irrefl _ hp)
  have hn : ¬ ∀ v, G.law p (G.infiniteEvent v) = 0 := by
    intro h
    exact (ne_of_gt hp) ((G.percolates_null_iff _).mpr h)
  push Not at hn
  obtain ⟨v, hv⟩ := hn
  have hvpos : 0 < (G.law p).real (G.infiniteEvent v) :=
    ENNReal.toReal_pos hv (measure_ne_top _ _)
  have hall := G.real_infiniteEvent_pos_all hconnected p hp0 hvpos
  obtain ⟨S, hS, horbit⟩ := hquasi
  have hSne : S.Nonempty := by
    obtain ⟨s, hs, _⟩ := horbit v
    exact ⟨s, hs⟩
  obtain ⟨s, hs, hmin⟩ := Set.exists_min_image S
    (fun o => (G.law p).real (G.infiniteEvent o)) hS hSne
  refine ⟨(G.law p).real (G.infiniteEvent s), hall s, ?_⟩
  intro o
  obtain ⟨t, ht, φ, rfl⟩ := horbit o
  rw [Aut.infiniteEvent_real]
  exact hmin t ht

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

end
end

end OAI
