import OAI.Probability.BenjaminiSchramm.ProbeEntropy
import OAI.Probability.BenjaminiSchramm.ProbabilityLower

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem markedConnection_entropy_comparison
    (G : BondGraph V E) (Q : Finset E) (x : V) (p q h : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) (hq : (q : ℝ) ∈ Set.Ioo 0 1)
    (hh : (h : ℝ) ∈ Set.Ioo 0 1) (d : ℕ)
    (hdeg : ∀ v, (Q.filter (fun e => v ∈ G e)).card ≤ d) :
    markedConnectionPolynomial G Q x h q ≤
      (2 + 2 * (d : ℝ) * ((p : ℝ) - q) ^ 2 / ((q : ℝ) * (1-q) * h)) *
        markedConnectionPolynomial G Q x h p := by
  let t := (markedClusterTree G Q x).forget
  have ht : ProbeTree.IsMarkSearch t := .mark (clusterSearch_markSearch G _ _ _)
  have hcost : ∀ l, ProbeTree.queries t l ≤ d * ProbeTree.marks t l := by
    simpa only [ProbeTree.Budget,zero_add] using markedClusterTree_budget G Q x d hdeg
  have hb := ProbeEntropy.successMass_transfer p q h hp hq hh t
  have hc := ProbeEntropy.totalQueries_le p h ht d hcost hh.1
  have hk := CriticalPercolation.FiniteEntropy.binaryDivergence_upper hq p.2
  have hkn : 0 ≤ CriticalPercolation.FiniteEntropy.binaryDivergence p q := by
    have hl := CriticalPercolation.FiniteEntropy.binaryDivergence_lower hq p.2
    nlinarith [sq_nonneg ((p : ℝ) - q)]
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hkn)
  have hn : 0 ≤ (d : ℝ) * ProbeTree.successMass p h t / h := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (ProbeTree.successMass_nonneg p h t)) hh.1.le
  have hk' := mul_le_mul_of_nonneg_right hk hn
  have hbound := hb.trans (add_le_add_right (hm.trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hk' (by norm_num : (0 : ℝ) ≤ 2))) _)
  rw [markedConnectionPolynomial_eq_tree,markedConnectionPolynomial_eq_tree]
  apply hbound.trans_eq
  field_simp [hh.1.ne',hq.1.ne',(sub_pos.mpr hq.2).ne']
  ring

theorem finiteClusterTail_eq_restricted_volume [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) (n : ℕ) (p : unitInterval) :
    finiteClusterTail G Q x n p =
      (law p).real {ω | ω ∩ (Q : Set E) ∈ volumeEvent G x n} := by
  let f (ω : Set E) : ℝ := if n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard then 1 else 0
  have hf : ∀ ω, f ω = f (ω ∩ (Q : Set E)) := by
    intro ω
    simp only [f,Set.inter_assoc,Set.inter_self]
  have he : (∫ ω, f ω ∂law p) = finiteClusterTail G Q x n p := by
    rw [integral_eq_bernoulliPolynomial Q p f hf]
    apply bernoulliPolynomial_congr
    intro ω hω
    simp only [f,finiteClusterTailIndicator,
      Set.inter_eq_left.mpr (show (ω : Set E) ⊆ Q from hω),
      ←coe_finiteRootComponent,Set.ncard_coe_finset]
  rw [←he]
  have hset : MeasurableSet {ω : Set E | ω ∩ (Q : Set E) ∈ volumeEvent G x n} := by
    exact (measurableSet_volumeEvent G x n).preimage (measurable_inter_const _)
  rw [←integral_event_indicator p _ hset]
  apply integral_congr_ae
  filter_upwards with ω
  have hfinite := cluster_finite_of_finite_edges G
    (ω := ω ∩ (Q : Set E)) (Q.finite_toSet.subset Set.inter_subset_right) x
  have hiff : ω ∩ (Q : Set E) ∈ volumeEvent G x n ↔
      n ≤ (cluster G (ω ∩ (Q : Set E)) x).ncard := by
    change (n : ℕ∞) ≤ (cluster G (ω ∩ (Q : Set E)) x).encard ↔ _
    rw [←hfinite.cast_ncard_eq]
    exact_mod_cast Iff.rfl
  simp only [f,hiff]

theorem finiteWitness_restricted_probability_tendsto [Encodable E]
    (A : Set (Set E)) (hA : IsUpperSet A) (hf : FiniteWitness A) (p : unitInterval) :
    Tendsto (fun k => (law p).real {ω : Set E |
      ω ∩ (edgeExhaustion (E := E) k : Set E) ∈ A}) atTop (𝓝 ((law p).real A)) := by
  have hmono : Monotone (fun k => {ω : Set E |
      ω ∩ (edgeExhaustion (E := E) k : Set E) ∈ A}) := by
    intro k l h ω hω
    exact hA (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
  have hh := tendsto_measure_iUnion_atTop (μ := law p) hmono
  rw [←witness_eq_union A hA hf] at hh
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hh

theorem volumeEvent_upper (G : BondGraph V E) (x : V) (n : ℕ) :
    IsUpperSet (volumeEvent G x n) := by
  rw [volumeEvent_eq_clusterLarge G x n]
  exact clusterLarge_upper G x n

theorem volumeEvent_finiteWitness (G : BondGraph V E) (x : V) (n : ℕ) :
    FiniteWitness (volumeEvent G x n) := by
  rw [volumeEvent_eq_clusterLarge G x n]
  exact finiteWitness_clusterLarge G x n

theorem volume_probability_le_of_finite_tails [Countable E]
    (G : BondGraph V E) (x : V) (n : ℕ) (p : unitInterval) (B : ℝ)
    (hB : ∀ Q : Finset E, finiteClusterTail G Q x n p ≤ B) :
    (law p).real (volumeEvent G x n) ≤ B := by
  let : Encodable E := Encodable.ofCountable E
  have hr := finiteWitness_restricted_probability_tendsto (volumeEvent G x n)
    (volumeEvent_upper G x n) (volumeEvent_finiteWitness G x n) p
  have hseq (k : ℕ) : (law p).real {ω : Set E |
      ω ∩ (edgeExhaustion (E := E) k : Set E) ∈ volumeEvent G x n} ≤ B :=
    (finiteClusterTail_eq_restricted_volume G (edgeExhaustion (E := E) k) x n p).symm.le.trans (hB _)
  exact le_of_tendsto hr (Eventually.of_forall hseq)

theorem percolationProbability_le_of_marked_bounds [Countable E]
    (G : BondGraph V E) (x : V) (p h : unitInterval) (hh : 0 < (h : ℝ)) (B : ℝ)
    (hB : ∀ Q : Finset E, markedConnectionPolynomial G Q x h p ≤ B) :
    percolationProbability G p x ≤ 2 * B := by
  obtain ⟨n,hn⟩ := exists_nat_ge (1 / (h : ℝ))
  have hprod : 1 ≤ (h : ℝ) * n := by
    have he := (div_le_iff₀ hh).mp hn
    linarith
  apply (measureReal_mono (μ := law p) (h₂ := measure_ne_top _ _) ?_).trans
    (volume_probability_le_of_finite_tails G x n p (2 * B) (fun Q =>
      (finiteClusterTail_le_markedConnection G Q x n p h hprod).trans
        (mul_le_mul_of_nonneg_left (hB Q) (by norm_num : (0 : ℝ) ≤ 2))))
  intro ω hω
  change (n : ℕ∞) ≤ (cluster G ω x).encard
  rw [Set.encard_eq_top hω]
  exact le_top

end Percolation.BenjaminiSchramm

end OAI
