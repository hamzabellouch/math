import OAI.GroupTheory.PolycyclicRecognition.Geometry.UniformCartanPublishedCharts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoarsePairHeight

namespace OAI

/-! # Uniform bounded Cartan height for arbitrary coarse inverse pairs -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

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
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)


local notation "Eall" => M.samplingPolytope T hunimod eW

theorem exists_uniform_coarse_cartan_height
    (hExp : IsGroupExponential Exp)
    (dixmier : DixmierExponentialInput (E := EG) (G := G))
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
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
    {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (rem : RemezPolynomialInput)
    (sourceInputs : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s)))
    (sourceDynkin : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i)
      (J : NilpotentLieModel (M.coneWordIdeal (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s)))),
      NilpotentDynkinExpansionInput J.modelSpace J.carrier)
    (targetInputs : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) (M.sampling_linear_weight_ne_zero T hunimod eW) i s) A.val)))
    (metricInput : GeodesicMetricExistenceInput)
    (raySource : ∀ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount),
      M.PolarConeModelInputs F (positiveWeightRay
        ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))
    (rayTarget : ∀ i : Fin M.letterCount,
      M.PolarConeModelInputs F (positiveWeightRay
        (((M.supportIn T hunimod eW).weight i).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))
    (raySourceDynkin : ∀ (A : templateSymmetryGroup (M.supportIn T hunimod eW)) (i : Fin M.letterCount)
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay
        ((((M.supportIn T hunimod eW).weight i).comp A.val.toLinearMap).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (rayTargetDynkin : ∀ (i : Fin M.letterCount)
      (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal (positiveWeightRay
        (((M.supportIn T hunimod eW).weight i).comp
          (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))))),
      NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (c : ControlledContraction G)
    {P : Type*} {κ ξ ε : ℝ} (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ)
    (f g : P → G → G)
    (hf : ∀ p x y, dist (f p x) (f p y) ≤ κ * dist x y + ξ)
    (hg : ∀ p x y, dist (g p x) (g p y) ≤ κ * dist x y + ξ)
    (hgf : ∀ p x, dist (g p (f p x)) x ≤ ε)
    (hfg : ∀ p x, dist (f p (g p x)) x ≤ ε) :
    ∃ (A : P → templateSymmetryGroup (M.supportIn T hunimod eW))
      (B : ℝ), 0 ≤ B ∧ ∀ p x,
      ‖(π (f p x)).toAdd - ((π (f p 1)).toAdd + (A p).val (π x).toAdd)‖ ≤ B := by
  apply uniform_affine_height_of_coarse_inverse_pairs c hpath
    (M.supportIn T hunimod eW) π Kπ.coe_nonneg
    (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
    _ hκ hξ f g hf hg hgf hfg
  intro Λ hΛ
  let : MeasurableSpace (NormalizedPair G Λ) := borel _
  let : BorelSpace (NormalizedPair G Λ) := ⟨rfl⟩
  let : MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W) := borel _
  let : BorelSpace C((Fin (finrank ℝ H) → ℝ), W) := ⟨rfl⟩
  exact M.exists_uniform_cartan_height_of_published_charts T F hunimod eW
    hExp dixmier realize haarN haarD dynkinN dynkinD m π hπExp (hdec Λ) (hvan Λ)
    (by linarith) hπ hpath rem sourceInputs sourceDynkin targetInputs
    metricInput raySource rayTarget raySourceDynkin rayTargetDynkin

end PolycyclicRecognition.CartanWordModel

end

end OAI
