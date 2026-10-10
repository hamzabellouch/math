import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanErgodicLabel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairStationaryIncrement
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairLabelFunctions

namespace OAI

/-! # Finite stationary increments on actual Cartan rays -/

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
/-- Along each actual Cartan exponential ray, normalized increments
approach the finite canonical label set for every fixed ergodic probability. -/
theorem increments_tendsto_labels_of_ergodic_probability
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
    (v : H) :
    Filter.Tendsto (fun r : ℝ => ∫⁻ p,
      ENNReal.ofReal (infDist (r⁻¹ • pairHeight π (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) p)
        (Set.range (fun A : supportSymmetryGroup (M.supportIn T hunimod eW) =>
          A.val (eW (heightProjection T.character v))))) ∂μ)
      Filter.atTop (nhds 0) := by
  obtain ⟨A, _, hsub⟩ := M.exists_finite_label_of_ergodic_probability
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD
    hExp realize m μ hvan hΛ hLip b₀ hφ hpath
  let l : G →* Multiplicative W := A.val.toLinearMap.toAddMonoidHom.toMultiplicative.comp π
  let g : ℝ → G := fun r => Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))
  have hd : Continuous g := continuous_exp_line_of_published_realization T Exp hExp realize v
  obtain ⟨C, hC, hb⟩ := continuous_flow_coarse_bound g hd
    (by simp [g, hExp.map_zero]) (fun s t => hExp.map_add_smul v s t)
  apply normalized_pair_increments_tendsto_labels μ π l hLip.continuous hsub g
    (R := 2 * C) (by positivity)
  · intro r hr
    have h := hb r
    rw [abs_of_nonneg (by linarith : 0 ≤ r)] at h
    exact h.trans (by nlinarith)
  · exact ⟨A, rfl⟩
  · intro r _
    change A.val (π (Exp (r • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).toAdd = _
    simp only [hπExp, map_smul]

end PolycyclicRecognition.CartanWordModel

end

end OAI
