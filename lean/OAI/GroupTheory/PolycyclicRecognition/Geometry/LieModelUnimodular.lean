import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseModelUnimodular
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricQuasiEquivalence
import OAI.GroupTheory.PolycyclicRecognition.Lattices.SolvableLatticeRecognition
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieModelMetric

namespace OAI

/-!
# Unimodularity of the metric Lie model

Restrict the ambient quasi-isometry to an actual uniform lattice. Its
compact coset cover supplies coarse surjectivity, and its inherited
metric has finite balls. The previously proved metric Følner transfer
then makes the target Haar measure right invariant. No unimodularity
assumption is made about either ambient group.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric MeasureTheory

section MetricComparison

variable {S G : Type*} [Group S] [Group G]
  [MetricSpace S] [IsTopologicalGroup S] [IsIsometricSMul S S] [ProperSpace S]
  [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableMul G]

/-- The compact cover of a polycyclic uniform lattice and an ambient
quasi-isometry give right invariance of the target's actual Haar measure. -/
theorem IsUniformLattice.isMulRightInvariant_of_metricQuasiEquivalence
    {Λ : Subgroup S} (hΛ : IsUniformLattice Λ) (hpoly : IsPolycyclic Λ)
    (e : MetricQuasiEquivalence S G)
    (μ : Measure G) [μ.IsHaarMeasure] [Measure.InnerRegular μ] :
    μ.IsMulRightInvariant := by
  classical
  let : IsIsometricSMul Λ Λ := ⟨fun γ => Isometry.of_dist_eq (fun x y => by
    change dist ((γ : S) * (x : S)) ((γ : S) * (y : S)) = dist (x : S) (y : S)
    exact dist_mul_left (γ : S) (x : S) (y : S))⟩
  obtain ⟨K, C, K', C', E, hK, hC, hK', _hC', hE, hup, hlo, hsurj⟩ :=
    e.quasiIsometry_toFun
  obtain ⟨R, hR, hcover⟩ := hΛ.exists_covering_radius
  have hsurj' : ∀ y : G, ∃ x : Λ, dist y (e.toFun (x : S)) ≤ E + (K * R + C) := by
    intro y
    obtain ⟨s, hs⟩ := hsurj y
    obtain ⟨x, hx⟩ := hcover s
    refine ⟨x, (dist_triangle y (e.toFun s) (e.toFun (x : S))).trans ?_⟩
    exact add_le_add hs ((hup s (x : S)).trans
      (add_le_add (mul_le_mul_of_nonneg_left hx hK) le_rfl))
  have hE' : 0 ≤ E + (K * R + C) := by
    positivity
  exact isMulRightInvariant_of_coarse_virtualPolycyclic μ hpoly.isVirtuallyPolycyclic
    hΛ.finite_closedBall (fun x : Λ => e.toFun (x : S)) hE' hK' hsurj'
    (fun x y => hlo (x : S) (y : S))

end MetricComparison

open scoped Manifold

/-- The actual Lie model obtained by the CT metric comparison is
unimodular when its source contains the given uniform solvable lattice.
Farb–Weinberger is used only for polycyclicity of that lattice. -/
theorem SimplyConnectedSolvableLieModel.isMulRightInvariant_of_lattice_comparison
    (fw : FarbWeinbergerLatticeInput) (S T : SimplyConnectedSolvableLieModel)
    (Λ : Subgroup S.carrier) (hΛ : IsUniformLattice Λ)
    (dS : ProperChainMetric S.carrier) (dT : ProperChainMetric T.carrier)
    (e : letI := dS.compatibleMetric
      letI := dT.compatibleMetric
      MetricQuasiEquivalence S.carrier T.carrier)
    [MeasurableSpace T.carrier] [BorelSpace T.carrier]
    (μ : Measure T.carrier) [μ.IsHaarMeasure] [Measure.InnerRegular μ] :
    μ.IsMulRightInvariant := by
  let := dS.compatibleMetric
  let := dT.compatibleMetric
  let := dS.proper_compatibleMetric
  let := dT.proper_compatibleMetric
  let := dS.isometric_compatibleMetric
  let := dT.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : IsTopologicalGroup T.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, T.modelSpace)) ⊤
  exact hΛ.isMulRightInvariant_of_metricQuasiEquivalence (fw S Λ hΛ) e μ

end PolycyclicRecognition

end

end OAI
