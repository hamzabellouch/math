import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.SelectedFresh
import OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability
import OAI.Probability.CriticalPercolation.Criticality.FewOpenBonds
import OAI.Probability.CriticalPercolation.Exploration.FrontierDivergence

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*} [Countable E]

lemma measurableSet_fewOpenBonds (S : Set E) (N : ℕ) :
    MeasurableSet[blockSigma S] {ω : Set E | (S∩ω).ncard ≤ N} := by
  simpa only [Set.inter_comm,Set.preimage_ofPred_eq,Set.Iic,Function.comp_apply] using
    (measurableSet_Iic.preimage (measurable_ncard.comp (measurable_inter_block S)))
end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

def fewOpenFreshBoundary (X : Set E) (v : V) (N : ℕ) : Set (Set E) :=
  {ω | (G.cluster (ω∩X) v).Finite ∧ (G.freshClusterBoundary X v ω ∩ ω).ncard ≤ N}

lemma fewOpenFreshBoundary_probability_le (hl : G.LocallyFinite) (p : unitInterval)
    (X : Set E) (v : V) (N L : ℕ) :
    (G.law p).real (G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N) ≤
      (G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary X v ((N+1)*L)) +
        (N+1 : ℝ)*(1-(p:ℝ))^L := by
  let M := (N+1)*L
  let C : Set (Set E) := {ω | (G.cluster (ω∩X) v).Finite ∧
    M ≤ (G.freshClusterBoundary X v ω).ncard}
  let d : Set E → Finset E := fun ω => finiteSetChoice (G.freshClusterBoundary X v ω)
  let A : Finset E → Set (Set E) := fun S =>
    {ω | (((S : Set E)∩Xᶜ)∩ω).ncard ≤ N}
  have hC : MeasurableSet[blockSigma X] C := by
    have hf : MeasurableSet[blockSigma X] {ω | (G.cluster (ω∩X) v).Finite} := by
      let : MeasurableSpace (Set E) := blockSigma X
      simpa only [Function.comp_apply,Set.not_infinite] using
        (((G.measurable_infinite_cluster v).comp (measurable_inter_block X)).not).setOf
    exact hf.inter (measurableSet_Ici.preimage
      (measurable_ncard.comp (G.measurable_freshClusterBoundary X v)))
  have hd (S : Finset E) : MeasurableSet[blockSigma X] {ω | d ω=S} :=
    @measurableSet_finiteSetChoice (Set E) E (blockSigma X) inferInstance
      (G.freshClusterBoundary X v) (G.measurable_freshClusterBoundary X v) S
  have hA (S : Finset E) : MeasurableSet[blockSigma Xᶜ] (A S) :=
    blockSigma_mono Set.inter_subset_right _ (measurableSet_fewOpenBonds _ N)
  have he (ω : Set E) (hω : (G.cluster (ω∩X) v).Finite) :
      ((d ω : Set E)∩Xᶜ)=G.freshClusterBoundary X v ω := by
    change (finiteSetChoice (G.freshClusterBoundary X v ω) : Set E)∩Xᶜ = _
    have hf : (G.freshClusterBoundary X v ω).Finite :=
      (G.finite_cutEdges hl hω).subset Set.sdiff_subset
    rw [finiteSetChoice_coe hf]
    exact Set.inter_eq_left.mpr (Set.sdiff_subset_compl _ _)
  let r : ℝ := (N+1 : ℝ)*(1-(p:ℝ))^L
  have hr : 0 ≤ r := mul_nonneg (by positivity) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  have hb (ω : Set E) (hω : ω∈C) : (BernoulliProduct.law (fun _ : E => p)).real (A (d ω)) ≤ r := by
    change (BernoulliProduct.law (fun _ : E => p)).real
      {τ | (((d ω : Set E)∩Xᶜ)∩τ).ncard ≤ N} ≤ _
    rw [he ω hω.1]
    exact fewOpenBonds_probability_le p _
      ((G.finite_cutEdges hl hω.1).subset Set.sdiff_subset) N L hω.2
  have ht := selected_fresh_bound (fun _ : E => p) X Xᶜ disjoint_compl_right
    d A hd hA C hC r hr hb
  simp only [law_const] at ht
  change (G.law p).real (C∩selectedEvent d A) ≤ r*(G.law p).real C at ht
  have ht' : (G.law p).real (C∩selectedEvent d A) ≤ r :=
    ht.trans ((mul_le_mul_of_nonneg_left measureReal_le_one hr).trans_eq (mul_one r))
  have hsub : G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N ⊆
      (G.infiniteEvent v ∩ G.smallFreshBoundary X v M) ∪ (C∩selectedEvent d A) := by
    intro ω hω
    by_cases h : (G.freshClusterBoundary X v ω).ncard ≤ M
    · exact Or.inl ⟨hω.1,hω.2.1,h⟩
    · right
      refine ⟨⟨hω.2.1,(Nat.le_of_lt (Nat.lt_of_not_ge h))⟩,?_⟩
      change (((d ω : Set E)∩Xᶜ)∩ω).ncard ≤ N
      rw [he ω hω.2.1]
      exact hω.2.2
  exact ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
    (add_le_add_right ht' _)

theorem fewOpenFreshBoundary_probability_tendsto_zero
    (hl : G.LocallyFinite) (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ)<1)
    (X : ℕ → Set E) (hX : ∀ S : Finset E, ∀ᶠ n in atTop, (S : Set E) ⊆ X n)
    (v : V) (N : ℕ) :
    Tendsto (fun n => G.law p (G.infiniteEvent v ∩ G.fewOpenFreshBoundary (X n) v N))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun L : ℕ => (N+1 : ℝ)*(1-(p:ℝ))^L) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (sub_nonneg.mpr p.2.2) (by linarith : 1-(p:ℝ)<1)).const_mul (N+1 : ℝ)
  have ht : Tendsto (fun n => (G.law p).real
      (G.infiniteEvent v ∩ G.fewOpenFreshBoundary (X n) v N)) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun _ => lt_of_lt_of_le ha measureReal_nonneg)
    · intro b hb
      obtain ⟨L,hL⟩ := (hpow.eventually (gt_mem_nhds (half_pos hb))).exists
      have hs := G.smallFreshBoundary_probability_tendsto_zero hl p hp1 X hX v ((N+1)*L)
      have hsreal := ENNReal.tendsto_toReal ENNReal.zero_ne_top |>.comp hs
      simp only [ENNReal.toReal_zero,Function.comp_def] at hsreal
      change Tendsto (fun n => (G.law p).real
        (G.infiniteEvent v ∩ G.smallFreshBoundary (X n) v ((N+1)*L))) atTop (𝓝 0) at hsreal
      filter_upwards [hsreal.eventually (gt_mem_nhds (half_pos hb))] with n hn
      exact lt_of_le_of_lt (G.fewOpenFreshBoundary_probability_le hl p (X n) v N L)
        (by linarith)
  have hh := ENNReal.tendsto_ofReal ht
  simpa only [ENNReal.ofReal_zero,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh

end CriticalPercolation.BondGraph
end
end

end OAI
