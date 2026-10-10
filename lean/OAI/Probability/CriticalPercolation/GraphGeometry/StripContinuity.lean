import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
import OAI.Probability.CriticalPercolation.Gluing.MoveExit
import OAI.Probability.CriticalPercolation.Gluing.StripMoves

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma axisExit_mono_width (u v : V → ℝ) (A : Set V) (L D : ℝ) (b : Bool)
    {W M : ℝ} (h : W≤M) : G.axisExit u v A L W D b⊆G.axisExit u v A L M D b := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.axisExit_iff u v A L W D b ω).mp hω
  exact (G.axisExit_iff u v A L M D b ω).mpr
    ⟨a,ha,x,w,fun y hy => ⟨(hw y hy).1,(hw y hy).2.trans h⟩,hx⟩

lemma reachable_level_mem_exit_union (u v : V → ℝ) (A : Set V) (Q D : ℝ)
    (hD : 0≤D) (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    {ω : Set E} {a x : V} (ha : a∈A) (hva : |v a|<Q)
    (hw : (G.openGraph ω).Reachable a x) (hx : Q≤|v x|) :
    ω∈⋃ n : ℕ, G.axisExit v u A Q n D true∪G.axisExit v u A Q n D false := by
  obtain ⟨w⟩ := hw
  obtain ⟨M,hM⟩ := (w.support.toFinset.finite_toSet.image (fun x => |u x|)).bddAbove
  obtain ⟨n,hn⟩ := exists_nat_gt M
  apply Set.mem_iUnion.mpr
  refine ⟨n,G.axisExit_of_crossing v u A Q n D hD hv ha hva w hx ?_⟩
  intro y hy
  exact (hM (Set.mem_image_of_mem _ (by simpa using hy))).trans hn.le

theorem exists_transverse_exit_probability [Countable V] [Countable E]
    (u v : V → ℝ) (A : Set V) (W Q D : ℝ) (q : E → unitInterval) (r : ℝ)
    (hD : 0≤D) (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hA : ∀ a∈A, |v a|<Q)
    (hdir : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ a, (G.cluster ω a).Infinite →
      ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hprob : r<(BernoulliProduct.law q).real (G.seedStripInfinite v A W)) :
    ∃ M : ℕ, r<(BernoulliProduct.law q).real
      (G.axisExit v u A Q M D true∪G.axisExit v u A Q M D false) := by
  let B := fun n : ℕ => G.axisExit v u A Q n D true∪G.axisExit v u A Q n D false
  have hmono : Monotone B := fun n m hnm =>
    Set.union_subset_union (G.axisExit_mono_width v u A Q D true (Nat.cast_le.mpr hnm))
      (G.axisExit_mono_width v u A Q D false (Nat.cast_le.mpr hnm))
  have hsub : G.seedStripInfinite v A W ≤ᵐ[BernoulliProduct.law q] ⋃ n, B n := by
    filter_upwards [hdir] with ω hω
    intro hseed
    obtain ⟨a,ha,hi⟩ := hseed
    have hi' : (G.cluster ω a).Infinite := hi.mono (G.cluster_mono Set.inter_subset_left a)
    obtain ⟨n,hn⟩ := exists_nat_gt Q
    obtain ⟨x,hx,hvx⟩ := hω a hi' n
    exact G.reachable_level_mem_exit_union u v A Q D hD hv ha (hA a ha) hx
      (hn.le.trans (hvx.le.trans (le_abs_self _)))
  have hb : r<(BernoulliProduct.law q).real (⋃ n, B n) :=
    hprob.trans_le (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub))
  have ht := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact (hreal.eventually (lt_mem_nhds hb)).exists

lemma longitudinal_exit_probability [Countable V] [Countable E]
    (u v : V → ℝ) (A : Set V) (W U D : ℝ) (q : E → unitInterval) (r : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hA : ∀ a∈A, |u a|<U ∧ |v a|≤W)
    (hbox : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ a∈A,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (hprob : r<(BernoulliProduct.law q).real (G.seedStripInfinite v A W)) :
    r<(BernoulliProduct.law q).real
      (G.axisExit u v A U W D true∪G.axisExit u v A U W D false) := by
  apply hprob.trans_le
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hbox] with ω hω
  exact fun hseed => G.strip_cluster_gives_exit u v A W U D hD hu hA hseed hω

end CriticalPercolation.BondGraph
end
end
end

end OAI
