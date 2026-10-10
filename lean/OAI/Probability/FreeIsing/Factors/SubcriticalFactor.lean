import OAI.Probability.FreeIsing.Critical.ClusterFactorEnvironment
import OAI.Probability.FreeIsing.Trees.ClusterFactorEnvironment
import OAI.Probability.FreeIsing.Trees.ClusterFactorMap
import OAI.Probability.FreeIsing.Trees.ClusterInputSampler
import OAI.Probability.FreeIsing.Trees.EncodedClusterLaw

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem isFactorOfIID_of_cluster_input_law {d : ℕ} {theta : ℝ}
    (hLaw : HasFreeIsingLaw theta
      (Measure.map (ClusterFactorMap.factor theta) (ClusterInput.law d))) :
    IsFactorOfIID d theta := by
  obtain ⟨S, hS, hSlaw, hSeq⟩ := ClusterInput.exists_sampler d
  refine ⟨ClusterFactorMap.factor theta ∘ S,
    (ClusterFactorMap.measurable_factor theta).comp hS, ?_, ?_⟩
  · rw [← Measure.map_map (ClusterFactorMap.measurable_factor theta) hS, hSlaw]
    exact hLaw
  · intro g
    apply Filter.Eventually.of_forall
    intro U
    change ClusterFactorMap.factor theta (S (relabel g U)) = _
    rw [hSeq]
    exact ClusterFactorMap.factor_relabel g theta (S U)

theorem isFactorOfIID_of_ae_finite_coded_clusters {d : ℕ} {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hfinite : ∀ᵐ q ∂EdgeIIDLaw.codingMeasure d, ∀ v : TreeVertex d,
      {a | Relation.ReflTransGen
        (EncodedClusterLaw.environmentRelation theta q) v a}.Finite) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_cluster_input_law
  exact EncodedClusterLaw.hasFreeIsingLaw_factor_of_ae_finite h0 h1 hfinite

theorem isFactorOfIID_of_strict_uniqueness {d : ℕ} {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hsub : (d - 1 : ℕ) * theta < 1) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_ae_finite_coded_clusters h0 h1
  exact ClusterFactorMap.ae_all_finite_environment_clusters h0 h1 hsub

theorem isFactorOfIID_of_uniqueness {d : ℕ} (hd : 3 ≤ d) {theta : ℝ}
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1) (hc : (d - 1 : ℕ) * theta ≤ 1) :
    IsFactorOfIID d theta := by
  apply isFactorOfIID_of_ae_finite_coded_clusters h0 h1
  exact ClusterFactorMap.ae_all_finite_environment_clusters_critical hd h0 h1 hc

end Problem367

end

end OAI
