import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.BernoulliThinning

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def thinPercolatesEvent (ω : Set E) : Set (Set E) :=
  {η | ω∩η∈G.percolates}

lemma measurableSet_thinPercolatesEvent [Countable V] [Countable E] (ω : Set E) :
    MeasurableSet (G.thinPercolatesEvent ω) :=
  G.measurableSet_percolates.preimage
    (BernoulliProduct.measurable_intersection.comp (measurable_const.prodMk measurable_id))

lemma thinPercolatesEvent_upper (ω : Set E) : IsUpperSet (G.thinPercolatesEvent ω) :=
  fun _ _ h hη => G.percolates_mono (Set.inter_subset_inter_right _ h) hη

lemma law_thinPercolates_mono [Countable V] [Countable E] (ω : Set E)
    {p q : unitInterval} (hpq : p≤q) :
    G.law p (G.thinPercolatesEvent ω)≤G.law q (G.thinPercolatesEvent ω) := by
  simpa only [BernoulliProduct.law_const,law] using
    BernoulliProduct.law_mono_parameters hpq (G.thinPercolatesEvent ω)
      (G.measurableSet_thinPercolatesEvent ω) (G.thinPercolatesEvent_upper ω)

lemma law_map_intersection (p r : unitInterval) :
    ((G.law p).prod (G.law r)).map (fun z : Set E×Set E => z.1∩z.2)=G.law (p*r) := by
  simpa only [BernoulliProduct.law_const,law] using
    BernoulliProduct.law_map_intersection (E := E) p r

lemma thinning_null_ae_of_product_null [Countable V] [Countable E]
    (p r : unitInterval) (h : G.law (p*r) G.percolates=0) :
    ∀ᵐ ω ∂G.law p, G.law r (G.thinPercolatesEvent ω)=0 := by
  have hn : (G.law p).prod (G.law r)
      ((fun z : Set E×Set E => z.1∩z.2) ⁻¹' G.percolates)=0 := by
    rw [←Measure.map_apply BernoulliProduct.measurable_intersection G.measurableSet_percolates,
      G.law_map_intersection,h]
  exact Measure.measure_ae_null_of_prod_null hn

lemma critical_thinning_null_ae_fixed [Countable V] [Countable E]
    (r : unitInterval) (hr : r<1) :
    ∀ᵐ ω ∂G.law G.criticalProbability, G.law r (G.thinPercolatesEvent ω)=0 := by
  apply G.thinning_null_ae_of_product_null
  by_cases hp : G.criticalProbability=0
  · rw [hp,zero_mul,G.law_zero_percolates]
  · apply G.law_percolates_eq_zero_of_lt_critical
    have hp' : (0 : ℝ)<G.criticalProbability :=
      (show (0 : unitInterval)<G.criticalProbability from lt_of_le_of_ne bot_le (Ne.symm hp))
    have hr' : (r : ℝ)<1 := hr
    change (G.criticalProbability : ℝ)*(r : ℝ)<(G.criticalProbability : ℝ)
    nlinarith

theorem critical_thinning_null_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ∀ r : unitInterval, r<1 →
      G.law r (G.thinPercolatesEvent ω)=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨r,hmono,hr,hlim⟩ := exists_seq_strictMono_tendsto'
    (show (0 : unitInterval)<1 by norm_num)
  have hn : ∀ᵐ ω ∂G.law G.criticalProbability, ∀ n : ℕ,
      G.law (r n) (G.thinPercolatesEvent ω)=0 :=
    ae_all_iff.mpr (fun n => G.critical_thinning_null_ae_fixed (r n) (hr n).2)
  filter_upwards [hn] with ω hω
  intro q hq
  obtain ⟨n,hn⟩ := (hlim.eventually (lt_mem_nhds hq)).exists
  exact le_antisymm ((G.law_thinPercolates_mono ω hn.le).trans_eq (hω n)) bot_le

theorem critical_not_robust_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ¬∃ r : unitInterval,
      r<1 ∧ 0<G.law r (G.thinPercolatesEvent ω) := by
  filter_upwards [G.critical_thinning_null_ae hc hl] with ω hω
  rintro ⟨r,hr,hp⟩
  exact hp.ne' (hω r hr)

end CriticalPercolation.BondGraph
end
end

end OAI
