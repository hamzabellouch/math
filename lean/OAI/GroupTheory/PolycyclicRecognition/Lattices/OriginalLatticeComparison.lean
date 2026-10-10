import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseEquivalenceMetric
import OAI.GroupTheory.PolycyclicRecognition.Lattices.LatticeMetricChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModelMetric

namespace OAI

/-! # Metric comparison with the original finite-index lattice model -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

/-- The discrete finite-index and lattice comparisons become a metric
quasi-equivalence in the chosen ambient metric. The linear-chain condition
on the original group makes explicit the word-metric scope. -/
theorem nonempty_original_lattice_comparison
    {P : Type} [Group P] [MetricSpace P] [IsIsometricSMul P P]
    (CP : LinearMetricChains P)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : P) R).Finite)
    (Γ : Subgroup P) (hΓ : Γ.FiniteIndex)
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsUniformLattice Λ) (iso : Γ ≃* Λ) (dS : ProperChainMetric S.carrier) :
    letI := dS.compatibleMetric
    Nonempty (MetricQuasiEquivalence P S.carrier) := by
  let := hΓ
  let := dS.compatibleMetric
  let := dS.proper_compatibleMetric
  let := dS.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : IsIsometricSMul Λ Λ := ⟨fun γ => Isometry.of_dist_eq (fun x y => by
    change dist ((γ : S.carrier) * (x : S.carrier)) ((γ : S.carrier) * (y : S.carrier)) = _
    exact dist_mul_left (γ : S.carrier) (x : S.carrier) (y : S.carrier))⟩
  obtain ⟨CΛ⟩ := hΛ.nonempty_linearMetricChains dS.chains_compatibleMetric
  let ePΛ := ((finiteIndexCoarseEquivalence Γ).symm.trans
    (PolycyclicRecognition.MulEquiv.groupCoarseEquivalence iso)).metric
    CP CΛ hfinite hΛ.finite_closedBall
  obtain ⟨eΛS⟩ := hΛ.nonempty_metricQuasiEquivalence
  exact ⟨ePΛ.trans eΛS⟩

end PolycyclicRecognition

end

end OAI
