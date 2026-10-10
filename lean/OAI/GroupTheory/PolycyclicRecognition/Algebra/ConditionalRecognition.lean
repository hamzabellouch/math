import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicContractionModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicCartanHeightAssembly
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IntrinsicTraceFromHaar
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PublishedRecognitionInputs
import OAI.GroupTheory.PolycyclicRecognition.Lattices.OriginalLatticeComparison
import Mathlib.Algebra.Lie.CartanExists

namespace OAI

/-! # Quasi-isometric recognition from precisely stated published inputs

Geometric height bounds, smoothing, finite labels, and finiteness/duality
transfer reduce recognition to the elementary-amenable finiteness and
polynomial-growth hypotheses of `PublishedRecognitionInputs`.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory
open scoped Manifold NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

/-- The recognition and finite-index lattice conclusions for metrics
comparable to word metrics. Only the original comparison group needs an
explicit linear-chain witness; the target's given quasi-equivalence is used
directly. -/
theorem recognition_and_lattice_of_published_inputs
    (inputs : PublishedRecognitionInputs)
    {P J : Type} [Group P] [Group J] [MetricSpace P] [MetricSpace J]
    [IsIsometricSMul P P] [IsIsometricSMul J J] [Group.FG P] [Group.FG J]
    [DiscreteTopology J] [ProperSpace J]
    [MeasurableSpace J] [BorelSpace J] [MeasurableMul J]
    (e : MetricQuasiEquivalence P J) (hP : IsVirtuallyPolycyclic P)
    (CP : LinearMetricChains P)
    (hPfinite : ∀ r : ℝ, (Metric.closedBall (1 : P) r).Finite) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  classical
  obtain ⟨Γ, hΓ, S, Λ, hΛ, ⟨iso⟩⟩ :=
    exists_uniform_solvable_lattice_of_virtuallyPolycyclic inputs.dekimpe P hP
  obtain ⟨R, a, T, dS, dR, hmodel⟩ :=
    exists_intrinsic_height_model_with_controlled_contraction inputs.triangulable
      inputs.metric inputs.riemannian inputs.differential S
  let := dS.compatibleMetric
  let := dR.toProperChainMetric.compatibleMetric
  let := dS.proper_compatibleMetric
  let := dS.isometric_compatibleMetric
  let := dR.toProperChainMetric.proper_compatibleMetric
  let := dR.toProperChainMetric.isometric_compatibleMetric
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : IsTopologicalGroup R.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, R.modelSpace)) ⊤
  let : MeasurableSpace R.carrier := borel _
  let : BorelSpace R.carrier := ⟨rfl⟩
  obtain ⟨⟨eSR⟩, ⟨c⟩, q, Exp, π, hExp, hπExp, _, _, K, hK, hπLip⟩ := hmodel
  obtain ⟨ePS⟩ := nonempty_original_lattice_comparison CP hPfinite Γ hΓ S Λ hΛ iso dS
  let u := e.symm.trans (ePS.trans eSR)
  let m : Measure R.carrier := Measure.haar
  let : m.IsMulRightInvariant :=
    SimplyConnectedSolvableLieModel.isMulRightInvariant_of_lattice_comparison
      inputs.farbWeinberger S R Λ hΛ
      dS dR.toProperChainMetric eSR m
  have hπ : LipschitzWith (⟨K, hK⟩ : ℝ≥0) (fun g => (π g).toAdd) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    exact hπLip x y
  have hunimod (x : GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier) :
      LinearMap.trace ℝ _ (ad ℝ _ x) = 0 :=
    trace_ad_eq_zero_of_intrinsic_kernel_haar T q Exp hExp π hπ.continuous hπExp m x
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel ℝ
    (GroupLieAlgebra (𝓘(ℝ, R.modelSpace)) R.carrier)
  let H := LieSubalgebra.engel ℝ x
  let : H.IsCartanSubalgebra := hx
  obtain ⟨M⟩ := nonempty_cartanWordModel H T
  have hheight := M.exists_uniform_height_intrinsic T hunimod q Exp hExp
    m π hπExp hπ
    dR.minimizing_compatibleMetric inputs.remez inputs.metric
  exact recognition_and_lattice_of_uniform_normalized_height inputs.dekimpe
    inputs.liFiniteness
    inputs.elementaryAmenableFiniteness inputs.liDuality inputs.bieriDuality
    e hP hPfinite T _ q π Exp hExp hπExp u inputs.gromov (M.supportIn T hunimod q)
    hπ c dR.minimizing_compatibleMetric hheight

end PolycyclicRecognition

end

end OAI
