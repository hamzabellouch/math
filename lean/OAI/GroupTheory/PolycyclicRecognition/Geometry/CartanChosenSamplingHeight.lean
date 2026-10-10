import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedBoundedHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedSamplingGeometry
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentBasisWordChoices
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSamplingNonzero

namespace OAI

/-! # Choosing the remaining concrete sampling data -/

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
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
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

/-- All finite-dimensional sampling choices are made in the proof. The
remaining hypotheses are the explicit published inputs and the actual
Cartan model and canonical height. -/
theorem exists_bounded_height_of_published_inputs
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
  let bN := finBasis ℝ (cartanRootIdeal H)
  obtain ⟨γ, hγ, _⟩ := M.exists_maximizing_box_basis T hunimod eW bN
    (M.samplingPolytope T hunimod eW)
  let bD := finBasis ℝ H
  obtain ⟨d, βD, hDnil, hDletters, hβD⟩ := exists_nilpotent_basis_word_choices bD
  let : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier) :=
    F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)
  let : LieRing.IsNilpotent (GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier) :=
    F.D.tangent_nilpotent inferInstance
  obtain ⟨cN, hcN⟩ := LieModule.IsNilpotent.nilpotent ℝ
    (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)
    (GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier)
  obtain ⟨cD, hcD⟩ := LieModule.IsNilpotent.nilpotent ℝ
    (GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier)
    (GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier)
  obtain ⟨aN, _, haN⟩ := dynkinN F.ExpN F.isExpN cN hcN 2
  obtain ⟨aD, _, haD⟩ := dynkinD F.ExpD F.isExpD cD hcD 2
  have hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y := by
    intro x y
    simpa using (haN ![x, y]).symm
  have hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y := by
    intro x y
    simpa using (haD ![x, y]).symm
  obtain ⟨lo, hi, c, hlo, hhi, hc, hcost, hgap⟩ := M.exists_sampling_gap T hunimod eW
  obtain ⟨pivot, hpivot⟩ := M.exists_sampling_contact_pivots T hunimod eW
  let α := fun i => ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
  obtain ⟨v, hv⟩ := (dense_genericWeightDirections α (M.sampling_weight_ne_zero T hunimod eW)).nonempty
  obtain ⟨σ, hσ, _⟩ := exists_incident_chamber_of_generic α 0 hv
  let B := ∑ i, ‖α i‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport
      (M.samplingPolytope T hunimod eW) i ≤ B := by
    intro i
    rw [M.sampling_weightSupport_eq T hunimod eW]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (α j)) (Finset.mem_univ i)
  have hdim : 1 ≤ finrank ℝ (cartanRootIdeal H) := by
    have hn : 0 < finrank ℝ (cartanRootIdeal H) := Fin.pos_iff_nonempty.mpr inferInstance
    omega
  exact M.exists_uniform_published_bounded_height T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ (fun i => bD i) hDnil hDletters bD βD hβD
    aN hmN aD hmD rem hdim pivot (fun i => (hpivot i).1) (fun i => (hpivot i).2.1)
    (fun i => (hpivot i).2.2.1) (fun i => (hpivot i).2.2.2.1)
    hc.le hhi.le hB hcost hgap σ hσ.1 (M.sampling_linear_weight_ne_zero T hunimod eW)
    sourceInputs sourceDynkin targetInputs hweightB metricInput
    raySource rayTarget raySourceDynkin rayTargetDynkin

end PolycyclicRecognition.CartanWordModel

end

end OAI
