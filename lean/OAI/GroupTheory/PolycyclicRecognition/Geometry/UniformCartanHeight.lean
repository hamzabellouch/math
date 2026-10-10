import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanChosenSamplingHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNontrivialHeight

namespace OAI

/-! # Uniform Cartan height, including the zero-height branch -/

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
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

local notation "Eall" => M.samplingPolytope T hunimod eW

theorem exists_uniform_cartan_height
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
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
    :
    ∃ (A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW))
      (K : ℝ), 0 ≤ K ∧ ∀ p x,
      ‖(π (p.val.1 x)).toAdd - (A p).val (π x).toAdd‖ ≤ K := by
  classical
  rcases subsingleton_or_nontrivial W with hW | hW
  · let : Subsingleton W := hW
    refine ⟨fun _ => 1, 0, le_rfl, ?_⟩
    intro p x
    rw [show (π (p.val.1 x)).toAdd - ((1 : templateSymmetryGroup (M.supportIn T hunimod eW)).val)
      (π x).toAdd = 0 from Subsingleton.elim _ _, norm_zero]
  · let : Nontrivial W := hW
    let : Nonempty (Fin M.letterCount) := M.nonempty_letters_of_nontrivial_height T hunimod eW
    let : Nonempty (Fin (finrank ℝ (cartanRootIdeal H))) :=
      M.nonempty_root_coordinates_of_nonempty_letters
    exact M.exists_bounded_height_of_published_inputs T F hunimod eW
      hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
      π hπExp hdec hvan hΛ hπ hpath rem sourceInputs sourceDynkin targetInputs
      metricInput raySource rayTarget raySourceDynkin rayTargetDynkin

end PolycyclicRecognition.CartanWordModel

end

end OAI
