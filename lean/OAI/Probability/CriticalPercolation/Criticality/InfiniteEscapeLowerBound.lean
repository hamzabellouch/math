import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.InfiniteEventSubsetHit
import OAI.Probability.CriticalPercolation.Criticality.SharpnessPhi

namespace OAI

section
section CurrentModule8
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {E V : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma infinite_escape_lower_bound (hl : G.LocallyFinite)
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : p < q) (hq : q < 1)
    (o : V) (hflux : ∀ S : Set V, S.Finite → o ∈ S → 1 ≤ phi G p o S) :
    ((q : ℝ)-p)/(1+q-p) ≤ (G.law q).real (G.infiniteEvent o) := by
  let L := (Set.to_countable (Set.univ : Set V)).finiteExhaustion
  apply ge_of_tendsto (G.tendsto_real_hit_compl q L o)
  apply Eventually.of_forall
  intro n
  let K := G.incidentEdges (L n)
  have hK : K.Finite := finite_incident G hl (L.finite n)
  let := hK.fintype
  have hf : ∀ R : Set V, (L n)ᶜ ⊆ R → o ∉ R →
      1 ≤ boundaryFlux (G.restrictEdges K) (p : ℝ) o R := by
    intro R hR ho
    have hsub : Rᶜ ⊆ L n := by
      simpa only [compl_compl] using Set.compl_subset_compl.mpr hR
    have he := phi_eq_boundaryFlux G p o Rᶜ K hK (incident_mono G hsub)
    simp only [compl_compl] at he
    rw [← he]
    exact hflux Rᶜ ((L.finite n).subset hsub) ho
  exact (uniform_escape_lower_bound (G.restrictEdges K)
    ⟨hp, (show (p : ℝ)<q from hpq).trans (show (q : ℝ)<1 from hq)⟩
    hpq hq o (L n)ᶜ hf).trans (restricted_escape_le G q o (L n)ᶜ K hK)

theorem subcritical_finite_size (hl : G.LocallyFinite)
    (p : unitInterval) (hp : p < G.criticalProbability) (o : V) :
    ∃ S : Set V, S.Finite ∧ o ∈ S ∧ phi G p o S < 1 := by
  by_cases hp0 : (p : ℝ) = 0
  · exact ⟨{o},Set.finite_singleton o,Set.mem_singleton o,by simp [phi,hp0]⟩
  have hp_pos : 0 < (p : ℝ) := lt_of_le_of_ne p.property.1 (Ne.symm hp0)
  by_contra h
  have hflux : ∀ S : Set V, S.Finite → o ∈ S → 1 ≤ phi G p o S := by
    intro S hS ho
    exact le_of_not_gt (fun hh => h ⟨S,hS,ho,hh⟩)
  let q : unitInterval := ⟨((p : ℝ)+(G.criticalProbability : ℝ))/2, by
    constructor
    · linarith [p.property.1,G.criticalProbability.property.1]
    · linarith [p.property.2,G.criticalProbability.property.2]⟩
  have hpq : p < q := by
    change (p : ℝ) < ((p : ℝ)+(G.criticalProbability : ℝ))/2
    have hh : (p : ℝ) < G.criticalProbability := hp
    linarith
  have hqc : q < G.criticalProbability := by
    change ((p : ℝ)+(G.criticalProbability : ℝ))/2 < (G.criticalProbability : ℝ)
    have hh : (p : ℝ) < G.criticalProbability := hp
    linarith
  have hq1 : q < 1 := hqc.trans_le G.criticalProbability.property.2
  have hb := infinite_escape_lower_bound G hl p q hp_pos hpq hq1 o hflux
  have hz : (G.law q).real (G.infiniteEvent o) = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr
    apply measure_mono_null (show G.infiniteEvent o ⊆ G.percolates from fun _ hω => ⟨o,hω⟩)
    exact G.law_percolates_eq_zero_of_lt_critical hqc
  rw [hz] at hb
  have hd : 0 < (q : ℝ)-p := sub_pos.mpr hpq
  have hden : 0 < 1+(q : ℝ)-p := by linarith
  exact (not_le_of_gt (div_pos hd hden)) hb

end CriticalPercolation.Sharpness
end
end CurrentModule8

end

end OAI
