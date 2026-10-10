import OAI.Probability.FreeIsing.Critical.CodedPercolation
import OAI.Probability.FreeIsing.Trees.ClusterFactorEnvironment

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.ClusterFactorMap

variable {d : ℕ}

theorem ae_all_finite_environment_clusters_critical (hd : 3 ≤ d) {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hc : ((d - 1 : ℕ) : ℝ) * theta ≤ 1) :
    ∀ᵐ e ∂EdgeIIDLaw.codingMeasure d, ∀ o : TreeVertex d,
      {v | connected theta (e.1, (e.2, fun _ => 0)) o v}.Finite := by
  have hmp := EdgeIIDLaw.measurePreserving_splitVertexInputs d
  rw [← hmp.map_eq]
  apply (ae_map_iff hmp.measurable.aemeasurable
    (measurableSet_all_finite_environment theta)).mpr
  exact CodedPercolation.ae_all_finite_coded_clusters_critical hd h0 h1 hc

theorem ae_good_environment_critical (hd : 3 ≤ d) {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hc : ((d - 1 : ℕ) : ℝ) * theta ≤ 1) :
    ∀ᵐ e ∂EdgeIIDLaw.codingMeasure d,
      Function.Injective e.1 ∧ Equivalence (connected theta (e.1, (e.2, fun _ => 0))) ∧
      ∀ o : TreeVertex d, {v | connected theta (e.1, (e.2, fun _ => 0)) o v}.Finite := by
  let : IsProbabilityMeasure (labelMeasure d) := by
    unfold labelMeasure
    infer_instance
  have hm := (measurePreserving_fst (μ := labelMeasure d)
    (ν := EdgeIIDLaw.rowMeasure d)).quasiMeasurePreserving.ae
      (FiniteCluster.ae_uniform_markers_injective d)
  filter_upwards [hm, ae_all_finite_environment_clusters_critical hd h0 h1 hc] with e he hfin
  exact ⟨he, connected_equivalence theta (p := (e.1, (e.2, fun _ => 0))) he, hfin⟩

end Problem367.ClusterFactorMap

end

end OAI
