import OAI.GroupTheory.PolycyclicRecognition.Geometry.UniformCartanPublishedCharts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentPublishedInputs
import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntrinsicIdealNormality

namespace OAI

/-! # Choosing all nilpotent models in the uniform Cartan height theorem -/

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

/-- Factor models, cone models, charts and measures are selected internally
from the cited nilpotent existence, integration, Haar and Dynkin inputs. -/
theorem exists_uniform_height_of_published_inputs
    (nilp : NilpotentPublishedInputs)
    (integrateN : ∀ N : NilpotentLieModel (cartanRootIdeal H),
      NilpotentLieIntegrationInput (EN := N.modelSpace) (N := N.carrier) (EG := EG) (G := G))
    (integrateD : ∀ N : NilpotentLieModel H,
      NilpotentLieIntegrationInput (EN := N.modelSpace) (N := N.carrier) (EG := EG) (G := G))
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (dixmier : DixmierExponentialInput (E := EG) (G := G))
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ∀ Λ : ℝ≥0,
      letI : MeasurableSpace (NormalizedPair G Λ) := borel _
      letI : BorelSpace (NormalizedPair G Λ) := ⟨rfl⟩
      ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ Λ : ℝ≥0,
      letI : MeasurableSpace (NormalizedPair G Λ) := borel _
      letI : BorelSpace (NormalizedPair G Λ) := ⟨rfl⟩
      ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
        [ErgodicSMul G (NormalizedPair G Λ) μ],
        ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    {Kπ : ℝ≥0} (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (rem : RemezPolynomialInput) (metric : GeodesicMetricExistenceInput) :
    ∀ Λ : ℝ≥0, 2 ≤ (Λ : ℝ) →
      ∃ A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW),
        ∃ K : ℝ, 0 ≤ K ∧ ∀ p x,
          ‖(π (p.val.1 x)).toAdd - (A p).val (π x).toAdd‖ ≤ K := by
  obtain ⟨chart, hchart⟩ := (dixmier ⟨a, ⟨T⟩⟩).2 Exp hExp
  have hsurj : Function.Surjective Exp := by
    intro g
    obtain ⟨v, hv⟩ := chart.surjective g
    exact ⟨v, (hchart v).symm.trans hv⟩
  obtain ⟨F⟩ := nonempty_cartanFactorModel_of_published_inputs T hExp dixmier
    (nilp.existsModel _) (nilp.existsModel _) (nilp.haar _) (nilp.haar _)
    integrateN integrateD (fun N =>
      nilpotentIdealNormalityInput_of_intrinsic_exponential (nilp.haar _ N) Exp hExp hsurj)
  intro Λ hΛ
  let : MeasurableSpace (NormalizedPair G Λ) := borel _
  let : BorelSpace (NormalizedPair G Λ) := ⟨rfl⟩
  let : MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W) := borel _
  let : BorelSpace C((Fin (finrank ℝ H) → ℝ), W) := ⟨rfl⟩
  exact M.exists_uniform_cartan_height_of_published_charts T F hunimod eW
    hExp dixmier realize (nilp.haar _ F.N) (nilp.haar _ F.D)
    (nilp.dynkin _ F.N) (nilp.dynkin _ F.D) m π hπExp (hdec Λ) (hvan Λ)
    (by linarith) hπ hpath rem
    (fun _ _ => nilp.polar M F _) (fun _ _ J => nilp.dynkin _ J)
    (fun _ _ _ => nilp.polar M F _) metric
    (fun _ _ => nilp.polar M F _) (fun _ => nilp.polar M F _)
    (fun _ _ Q => nilp.dynkin _ Q) (fun _ Q => nilp.dynkin _ Q)

end PolycyclicRecognition.CartanWordModel

end

end OAI
