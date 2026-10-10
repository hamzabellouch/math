import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHeightPublishedAssembly
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicCartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.IntrinsicTriangularRealization
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CartanReducedCohomology
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedPairErgodicDecomposition

namespace OAI

/-! # The uniform height theorem with intrinsic Cartan factors

The factors, coordinates, realization, ergodic decomposition, reduced
cohomology, and polynomial and metric estimates are supplied by proved
constructions for the actual unimodular group.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Set
open scoped Manifold NNReal

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)

theorem exists_uniform_height_intrinsic
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    {Kπ : ℝ≥0} (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (rem : RemezPolynomialInput) (metric : GeodesicMetricExistenceInput) :
    ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
      ∃ A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW),
        ∃ K : ℝ, 0 ≤ K ∧ ∀ p x,
          ‖(π (p.val.1 x)).toAdd - (A p).val (π x).toAdd‖ ≤ K := by
  let nilp := nilpotentPublishedInputs
  obtain ⟨F⟩ := nonempty_intrinsic_cartanFactorModel T eW Exp hExp π hπ.continuous hπExp H
  let : IsTopologicalGroup F.N.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.N.modelSpace)) ⊤
  let : IsTopologicalGroup F.D.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤
  let : LocallyCompactSpace F.D.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.D.modelSpace))
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := (nilp.haar _ F.N).2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := (nilp.haar _ F.D).2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  let : SecondCountableTopology F.N.carrier := F.N.secondCountable_of_chart chartN
  let : SecondCountableTopology F.D.carrier := F.D.secondCountable_of_chart chartD
  let νD : Measure F.D.carrier := Measure.haar
  intro Λ hΛ
  let : MeasurableSpace (NormalizedPair G Λ) := borel _
  let : BorelSpace (NormalizedPair G Λ) := ⟨rfl⟩
  let : MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W) := borel _
  let : BorelSpace C((Fin (finrank ℝ H) → ℝ), W) := ⟨rfl⟩
  exact M.exists_uniform_cartan_height T F hunimod eW hExp
    (intrinsic_exponential_injective T Exp hExp) exponentialLinearRealizationInput_intrinsic
    (nilp.haar _ F.N) (nilp.haar _ F.D) (nilp.dynkin _ F.N) (nilp.dynkin _ F.D)
    chartN hchartN chartD hchartD m νD π hπExp normalizedPair_ergodicDecomposition
    (fun μ _ _ => (cartan_unitary_reduced_vanishing T F M hExp hunimod eW π hπExp
      hπ.continuous).to_reduced (ZeroMeanL2 (W := W) μ))
    (by linarith) hπ hpath rem
    (fun _ _ => nilp.polar M F _) (fun _ _ J => nilp.dynkin _ J)
    (fun _ _ _ => nilp.polar M F _) metric
    (fun _ _ => nilp.polar M F _) (fun _ => nilp.polar M F _)
    (fun _ _ Q => nilp.dynkin _ Q) (fun _ Q => nilp.dynkin _ Q)

end PolycyclicRecognition.CartanWordModel

end

end OAI
