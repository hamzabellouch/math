import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import OAI.Probability.CriticalPercolation.Modular.ModularClusterMass

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def massTailEvent (o v : V) (a : ℝ≥0∞) : Set (Set E) :=
  {ω | a<G.modularMass o (G.cluster ω v)}

lemma massTailEvent_upper (o v : V) (a : ℝ≥0∞) : IsUpperSet (G.massTailEvent o v a) :=
  fun _ _ h hh => hh.trans_le (G.modularMass_mono o (G.cluster_mono h v))

lemma massTailEvent_finiteWitness (o v : V) (a : ℝ≥0∞) :
    BernoulliProduct.HasFiniteOpenWitness (G.massTailEvent o v a) := by
  intro ω hω
  change a<∑' x, if x∈G.cluster ω v then G.stabilizerWeight o x else 0 at hω
  rw [ENNReal.tsum_eq_iSup_sum,lt_iSup_iff] at hω
  obtain ⟨S,hS⟩ := hω
  let T : Set V := (S : Set V) ∩ G.cluster ω v
  obtain ⟨s,hs,hsω,hTs⟩ := G.finite_subset_cluster_finite_witness
    (S.finite_toSet.inter_of_left _) (show T⊆G.cluster ω v from Set.inter_subset_right)
  refine ⟨s,hs,hsω,lt_of_lt_of_le hS ?_⟩
  change (∑ x∈S, if x∈G.cluster ω v then G.stabilizerWeight o x else 0) ≤
    ∑' x, if x∈G.cluster s v then G.stabilizerWeight o x else 0
  apply (Finset.sum_le_sum (fun x hx => ?_)).trans (ENNReal.sum_le_tsum S)
  by_cases hxω : x∈G.cluster ω v
  · rw [ite_eq_left hxω,ite_eq_left (hTs ⟨hx,hxω⟩)]
  · simp only [ite_eq_right hxω,zero_le]

lemma measurableSet_massTailEvent [Countable V] [Countable E] (o v : V) (a : ℝ≥0∞) :
    MeasurableSet (G.massTailEvent o v a) :=
  measurableSet_lt measurable_const (G.measurable_modularClusterMass o v)

lemma heavyClusterEvent_eq_iInter_massTail (o v : V) :
    G.heavyClusterEvent o v=⋂ n : ℕ, G.massTailEvent o v n := by
  ext ω
  simp only [heavyClusterEvent,massTailEvent,Set.mem_ofPred_eq,Set.mem_iInter]
  constructor
  · intro h n
    rw [h]
    exact ENNReal.natCast_lt_top n
  · intro h
    by_contra hn
    obtain ⟨n,hnn⟩ := exists_nat_gt (G.modularMass o (G.cluster ω v)).toReal
    have hlt : (n:ℝ≥0∞)<G.modularMass o (G.cluster ω v) := h n
    have hh := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top n) hn).mpr hlt
    simp only [ENNReal.toReal_natCast] at hh
    exact (lt_irrefl _) (hh.trans hnn)

lemma massTailEvent_antitone (o v : V) : Antitone (fun n : ℕ => G.massTailEvent o v n) := by
  intro n m h ω hω
  exact lt_of_le_of_lt (show (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) by exact_mod_cast h) hω

lemma tendsto_real_massTail [Countable V] [Countable E] (p : unitInterval) (o v : V) :
    Tendsto (fun n : ℕ => (G.law p).real (G.massTailEvent o v n)) atTop
      (𝓝 ((G.law p).real (G.heavyClusterEvent o v))) := by
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n : ℕ => (G.measurableSet_massTailEvent o v n).nullMeasurableSet)
    (G.massTailEvent_antitone o v) ⟨0,measure_ne_top _ _⟩
  rw [←G.heavyClusterEvent_eq_iInter_massTail] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma harris_heavyClusterEvent [Countable V] [Countable E] (p : unitInterval) (o x y : V) :
    (G.law p).real (G.heavyClusterEvent o x) * (G.law p).real (G.heavyClusterEvent o y) ≤
      (G.law p).real (G.heavyClusterEvent o x ∩ G.heavyClusterEvent o y) := by
  have hlim := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n : ℕ => ((G.measurableSet_massTailEvent o x n).inter
      (G.measurableSet_massTailEvent o y n)).nullMeasurableSet)
    (show Antitone (fun n : ℕ => G.massTailEvent o x n ∩ G.massTailEvent o y n) from
      fun _ _ h => Set.inter_subset_inter (G.massTailEvent_antitone o x h)
        (G.massTailEvent_antitone o y h)) ⟨0,measure_ne_top _ _⟩
  rw [Set.iInter_inter_distrib,←G.heavyClusterEvent_eq_iInter_massTail,
    ←G.heavyClusterEvent_eq_iInter_massTail] at hlim
  apply le_of_tendsto_of_tendsto
    ((G.tendsto_real_massTail p o x).mul (G.tendsto_real_massTail p o y))
    ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim)
  apply Eventually.of_forall
  intro n
  simpa only [BernoulliProduct.law_const,BondGraph.law,measureReal_def,Function.comp_apply] using
    BernoulliProduct.harris_finiteWitness (fun _ : E => p)
      (G.massTailEvent o x n) (G.massTailEvent o y n)
      (G.massTailEvent_upper o x n) (G.massTailEvent_upper o y n)
      (G.massTailEvent_finiteWitness o x n) (G.massTailEvent_finiteWitness o y n)

end CriticalPercolation.BondGraph
end
end

end OAI
