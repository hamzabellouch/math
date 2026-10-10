import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanStationaryTemplateLabel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairMeanApproximation

namespace OAI

/-! # Finite stationary labels from the published reduced-cohomology input -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [SecondCountableTopology G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- The precise published reduced-cohomology input gives a finite linear
label and the fixed-measure sublinear estimate on the actual pair space. -/
theorem exists_template_label_of_ergodic_probability
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    [ErgodicSMul G (NormalizedPair G Λ) μ] [μ.InnerRegularCompactLTTop]
    (hvan : ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {K : ℝ≥0}
    (hLip : LipschitzWith K (fun g => (π g).toAdd))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    : ∃ A : templateSymmetryGroup (M.supportIn T hunimod eW),
      (∀ g, (normalizedPairMeanSlope μ π hLip.continuous g).toAdd = A.val (π g).toAdd) ∧
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
        ‖pairHeightL2 μ π hLip.continuous g - Lp.const 2 μ (A.val (π g).toAdd)‖ ≤
          ε * dist 1 g + B := by
  let l := normalizedPairMeanSlope μ π hLip.continuous
  have hl : Continuous fun g => (l g).toAdd := continuous_normalizedPairMeanSlope μ π hLip.continuous
  obtain ⟨ψ, hψ, hψm, happrox⟩ := normalizedPairMean_coboundary_approximation μ hvan π hLip.continuous
  have hsub := pairHeight_sublinear_of_minimizing_paths μ π l hLip.continuous ψ hψ happrox hpath
  have hbound : ∀ g, ‖(l g).toAdd‖ ≤ (K : ℝ) * Λ * dist 1 g :=
    norm_normalizedPairMeanSlope_le μ π hLip
  have hpoint : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ (K : ℝ) * dist x y := by
    intro x y
    simpa only [dist_eq_norm] using hLip.dist_le_mul x y
  obtain ⟨A, hA⟩ := M.exists_template_label_of_stationary_mean T F hunimod eW π hπExp
    chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD hExp realize m μ l
    hLip.continuous hl hΛ K.coe_nonneg (mul_nonneg K.coe_nonneg Λ.coe_nonneg)
    hpoint hbound hsub b₀ hφ hpath ψ hψ hψm happrox
  refine ⟨A, hA, ?_⟩
  simpa only [hA] using hsub

end PolycyclicRecognition.CartanWordModel

end

end OAI
