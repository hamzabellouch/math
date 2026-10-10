import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorCharts
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ModelDensityOccupation

namespace OAI

/-! # The second-factor occupation estimate on the actual Cartan model -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule MeasureTheory Filter
open scoped Manifold Topology NNReal

variable {EG G I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]

omit [SimplyConnectedSpace G] in
include T in
/-- Every fixed second-factor move changes the actual joint chart law by
a vanishing amount. The first-factor sampling and deterministic suffix
may vary arbitrarily through their coordinate chart and basepoint. -/
theorem cartan_density_occupation_error_tendsto_zero
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k c : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    (aD : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    {m : ℕ} (bN : ℝ → Basis (Fin m) ℝ (cartanRootIdeal H))
    (μ : ProbabilityMeasure (Fin m → ℝ))
    (ρ : (Fin (finrank ℝ H) → ℝ) → ℝ) (hc : Continuous ρ)
    (hi : Integrable ρ volume) (hp : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z = 1)
    (p : ℝ → NormalizedPair G Λ) (x : ℝ → G) (suffix : ℝ → F.N.carrier)
    (v : H) (f : C(NormalizedPair G Λ, ℝ)) :
    let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
      (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0)
    let chart := fun r => coordinateChartPoint (p r) (x r) F.inclusionN F.inclusionD
      (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (suffix r)
    let law := fun r => productOccupationLaw μ
      (densityProbabilityMeasure volume ρ hi hp hmass) (chart r)
    Tendsto (fun r : ℝ =>
      (∫ y, f ((F.inclusionD (F.ExpD (F.D.equiv v)))⁻¹ • y) ∂(law r : Measure _)) -
        ∫ y, f y ∂(law r : Measure _)) atTop (𝓝 0) := by
  let bD := fun r => exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords k) β)
    (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (max (Real.log r) 0)
  let chart := fun r => coordinateChartPoint (p r) (x r) F.inclusionN F.inclusionD
    (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (suffix r)
  have hmeas (r : ℝ) : Measurable (chart r) := by
    apply Continuous.measurable
    apply continuous_coordinateChartPoint
    · exact F.closedN.continuous.comp
        (continuous_model_exp_coordinates haarN F.ExpN F.isExpN F.N.equiv
          (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T)) (bN r))
    · exact F.closedD.continuous.comp
        (continuous_model_exp_coordinates haarD F.ExpD F.isExpD F.D.equiv
          (F.D.tangent_nilpotent inferInstance) (bD r))
  apply model_density_occupation_error_tendsto_zero haarD F.ExpD F.isExpD F.D.equiv
    (F.D.tangent_nilpotent inferInstance) X hk hletters b₀ (fun _ : I => 1) (by norm_num)
    Real.log Real.tendsto_log_atTop β hβ aD hm v μ ρ hc hi hp hmass chart hmeas
    (F.inclusionD (F.ExpD (F.D.equiv v)))⁻¹ _ f
  intro r u z
  exact coordinateChartPoint_right (p r) (x r) F.inclusionN F.inclusionD
    (F.ExpN ∘ F.N.equiv) (F.ExpD ∘ F.D.equiv) (bN r) (bD r) (suffix r) aD
    (model_binary_dynkin F.D.equiv F.ExpD aD hm) v (u, z)

end PolycyclicRecognition

end

end OAI
