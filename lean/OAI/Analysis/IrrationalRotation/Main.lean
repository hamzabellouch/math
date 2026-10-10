import Mathlib
import OAI.Analysis.IrrationalRotation.PrescribedAngle
import OAI.Analysis.IrrationalRotation.Sampling.ProductSourceSamplingFinal
import OAI.Analysis.IrrationalRotation.Product.ProductRealizationAssembly
import OAI.Analysis.IrrationalRotation.Rotation.RotationHyperfinite
import OAI.Analysis.IrrationalRotation.Rotation.RotationFactorStructure
import OAI.Analysis.IrrationalRotation.Rotation.CircleTruncationBound
import OAI.Analysis.IrrationalRotation.Rotation.CircleOrderedTransfer
import OAI.Analysis.IrrationalRotation.Product.ProductFactorComplete
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitMarginalLaws
import OAI.Analysis.IrrationalRotation.Rotation.CircleTailAttenuation
import OAI.Analysis.IrrationalRotation.Couplings.CircleConditionalLabels
import OAI.Analysis.IrrationalRotation.Couplings.SourceCouplingMarginals
import OAI.Analysis.IrrationalRotation.Rotation.CircleParametersExistence
import OAI.Analysis.IrrationalRotation.Operators.FullAffiliatedTransport
import OAI.Analysis.IrrationalRotation.Analysis.OrdinaryTailNonmembership
import OAI.Analysis.IrrationalRotation.Rotation.PositiveDiagonalAlgebra
import OAI.Analysis.IrrationalRotation.Sampling.ScalarSamplingSeparated
import OAI.Analysis.IrrationalRotation.Spectral.ProductPolarComplete
import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphs
import OAI.Analysis.IrrationalRotation.Operators.OperatorCompactTransfer
import OAI.Analysis.IrrationalRotation.Sampling.LargePhaseAssembly
import OAI.Analysis.IrrationalRotation.Spectral.ProductSpectralBundle
import OAI.Analysis.IrrationalRotation.Spectral.RotationDeterminant
import OAI.Analysis.IrrationalRotation.Analysis.TriangularLawProperties
import OAI.Analysis.IrrationalRotation.Analysis.ScalarMultiplierFields
import OAI.Analysis.IrrationalRotation.Model.Analytic
import OAI.Analysis.IrrationalRotation.Operators.CommutantProper
import OAI.Analysis.IrrationalRotation.Operators.HyperinvariantProjection
import OAI.Analysis.IrrationalRotation.Operators.CommutantAlgebra
import OAI.Analysis.IrrationalRotation.Analysis.FiniteConvolution
import OAI.Analysis.IrrationalRotation.Rotation.UniformRotationAverage
import OAI.Analysis.IrrationalRotation.Couplings.ProductDensityLimit
import OAI.Analysis.IrrationalRotation.Couplings.ConditionalConvolution
import OAI.Analysis.IrrationalRotation.Rotation.CircleMeasurableObstruction
import OAI.Analysis.IrrationalRotation.Analysis.ContinuousCounterexampleAssembly
import OAI.Analysis.IrrationalRotation.Operators.HilbertConsequence
import OAI.Analysis.IrrationalRotation.Model.Conjugation
import OAI.Analysis.IrrationalRotation.Analysis.ChoKoLeeCompleteComparison
import OAI.Analysis.IrrationalRotation.Couplings.ProductBiasedIdentity
import OAI.Analysis.IrrationalRotation.Couplings.ProductPairIdentity

namespace OAI

/-! Irrational rotation counterexamples, product realizations, and transitive commutants. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace Invariant233.Results

theorem rotation_hyperfinite (θ : ℝ)
    (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (hθ : Irrational θ) :
    IsHyperfinite (Rotation.algebra θ) := by
  exact Rotation.isHyperfinite_algebra hθ

theorem circle_parameters_exist (θ : ℝ)
    (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (hθ : Irrational θ) :
    ∃ p : CircleParameterData, CircleParameterLaws θ p :=
  Invariant233.exists_circle_parameters hθ

section Operators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem commutant_properness (T : H →L[ℂ] H)
    (hT : ¬ ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) :
    Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) ≠ ⊤ :=
  Invariant233.centralizer_singleton_ne_top_of_nonscalar T hT

theorem commutant_affine_shift (T : H →L[ℂ] H) :
    Subalgebra.centralizer ℂ ({1 + T} : Set (H →L[ℂ] H)) =
      Subalgebra.centralizer ℂ ({T} : Set (H →L[ℂ] H)) :=
  Invariant233.centralizer_singleton_one_add T

theorem commutant_algebra (T : H →L[ℂ] H)
    (hT : ¬ ∃ c : ℂ, T = c • (1 : H →L[ℂ] H)) :
    operatorCommutant T ≠ ⊤ ∧ IsStronglyClosed (operatorCommutant T) ∧
      (IsTransitive (operatorCommutant T) ↔ HasNoNontrivialHyperinvariantSubspace T) :=
  Invariant233.commutant_algebra_properties T hT

variable [CompleteSpace H]

theorem hyperinvariant_projection_mem
    (M : VonNeumannAlgebra H) {T p : H →L[ℂ] H}
    (hT : T ∈ M) (hp : IsStarProjection p)
    (hhyper : ∀ A : H →L[ℂ] H, Commute A T →
      p.range ∈ Module.End.invtSubmodule A) :
    p ∈ M ∧ (1 - p) * T * p = 0 :=
  Invariant233.hyperinvariant_projection_mem M hT hp hhyper

end Operators

theorem finite_convolution_uniform_lower_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε > 0, ∀ a b : InvariantProjection.FiniteConvolution.Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a (InvariantProjection.FiniteConvolution.center K)‖ →
      δ ≤ ‖b (InvariantProjection.FiniteConvolution.center K)‖ →
      ∃ n : Fin (2 * K + 1),
        ε ≤ ‖InvariantProjection.FiniteConvolution.lowProduct a b n‖ :=
  InvariantProjection.FiniteConvolution.uniform_lower_bound K D δ hδ

theorem uniform_irrational_rotation_average {θ : ℝ} (hθ : Irrational θ)
    (f : C(Circle, ℝ)) :
    TendstoUniformly
      (fun n x => birkhoffAverage ℝ (fun y : Circle => y + (θ : Circle)) f n x)
      (fun _ => ∫ x, f x ∂AddCircle.haarAddCircle) atTop :=
  InvariantProjection.UniformRotationAverage.tendstoUniformly_real hθ f

end Invariant233.Results

namespace Invariant233

theorem product_density_bound
    {Ω : ℕ → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : (i : ℕ) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {h : (i : ℕ) → Ω i → ℝ} {C : ℝ}
    (hh : ∀ i, MemLp (h i) 2 (μ i))
    (hnonneg : ∀ i x, 0 ≤ h i x)
    (hmean : ∀ i, ∫ x, h i x ∂μ i = 1)
    (hsum : Summable (fun i => (eLpNorm (fun x => h i x - 1) 2 (μ i)).toReal ^ 2))
    (hC : (∑' i, (eLpNorm (fun x => h i x - 1) 2 (μ i)).toReal ^ 2) ≤ C) :
    ∃ H : ((i : ℕ) → Ω i) → ℝ,
      MemLp H 2 (Measure.infinitePi μ) ∧
      (0 ≤ᵐ[Measure.infinitePi μ] H) ∧
      (∫ x, H x ∂Measure.infinitePi μ) = 1 ∧
      eLpNorm H 2 (Measure.infinitePi μ) ≤ ENNReal.ofReal (Real.exp (C / 2)) ∧
      (Measure.infinitePi μ).withDensity (fun x => ENNReal.ofReal (H x)) =
        Measure.infinitePi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (h i x))) :=
  ProductDensity.exists_product_density_of_norm hh hnonneg hmean hsum hC

end Invariant233

namespace Invariant233

theorem conditional_convolution
    (K : ℕ) (D a : ℝ) (ha : 0 < a) :
    ∃ ε > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (c η δ : ℝ),
      0 ≤ η → 0 ≤ δ → ∀ _ : InvariantProjection.ConditionalConvolution.Data Ω μ K D a c η δ,
      c * ε ≤ ((2 * K + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) :=
  InvariantProjection.ConditionalConvolution.conditional_convolution_obstruction K D a ha

end Invariant233

namespace Invariant233
open scoped ENNReal

theorem scalar_multiplier_fields
    {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Countable ι]
    (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (L2Multiplication.multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x)) ∧
      (∀ G : X → E →L[ℂ] E,
        (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => G x (f x)) → F =ᵐ[μ] G) ∧
      (∀ f : Lp E 2 μ, A.adjoint f =ᵐ[μ] fun x => (F x).adjoint (f x)) ∧
      (∀ (B : Lp E 2 μ →L[ℂ] Lp E 2 μ) (G : X → E →L[ℂ] E),
        (∀ f : Lp E 2 μ, B f =ᵐ[μ] fun x => G x (f x)) →
        ∀ f : Lp E 2 μ, (A * B) f =ᵐ[μ] fun x => (F x * G x) (f x)) ∧
      (IsStarProjection A → ∀ᵐ x ∂μ, IsStarProjection (F x)) :=
  L2Multiplication.scalar_multiplier_fields_complete b A hA

end Invariant233

namespace Invariant233

theorem rational_graphs {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      p.RationalGraphIdentities θ F := by
  exact hp.exists_rational_graph_field hmem hP hT

end Invariant233

namespace Invariant233.Results

theorem continuous_counterexample_quasinilpotent (θ : ℝ) (hθ : Irrational θ)
    (f : C(Circle, ℝ)) (hf : IsContinuousCircleWeight f) :
    Rotation.weightedReal θ f ≠ 0 ∧ NormQuasinilpotent (Rotation.weightedReal θ f) ∧
      vectorFugledeKadisonDeterminant Rotation.vacuum (Rotation.weightedReal θ f) = 0 :=
  Rotation.continuous_weight_spectral_bundle θ hθ f hf

theorem product_triangular_law_properties (I : Finset ℕ) :
    ProductModel.TriangularLawProperties I :=
  ProductModel.triangularLaw_properties I

end Invariant233.Results

namespace Invariant233
open scoped ENNReal BigOperators

theorem product_quasinilpotent
    (m : ℕ → ℕ) (hm : ∀ j, 0 < m j)
    (K C : ℕ → ℝ) (hK : ∀ j, 1 ≤ K j) (hC : ∀ j, K j ^ 2 ≤ C j)
    (e : ℕ ≃ Σ j, Fin (m j)) (θ : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1) (hθsum : Summable θ)
    (hθlower : ∀ i, 1 / ((m (e i).1 : ℝ) * K (e i).1) ≤ θ i) :
    let c : ℕ → ℝ := fun i => C (e i).1
    HasNegInfiniteLogIntegral ProductModel.baseMeasure (ProductModel.weight θ c) ∧
      ProductModel.weightedOperator θ c ∈ ProductModel.factor θ ∧
      ProductModel.weightedOperator θ c ≠ 0 ∧
      NormQuasinilpotent (ProductModel.weightedOperator θ c) ∧
      vectorFugledeKadisonDeterminant ProductModel.traceVector
        (ProductModel.weightedOperator θ c) = 0 ∧
      spectrum ℂ (ProductModel.weightedOperator θ c) = {0} ∧
      ∀ (I : Finset ℕ) (n : ℕ),
        ‖ProductModel.weightedOperator θ c ^ n‖ ≤
          Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  dsimp
  obtain ⟨hlog, hmem, hne, hqn, hdet, hspec⟩ :=
    ProductModel.spectral_bundle_of_block_bounds m hm K C hK hC e θ
      hθsum hθ01 hθlower
  refine ⟨hlog, hmem, hne, hqn, hdet, hspec, ?_⟩
  intro I n
  exact ProductModel.norm_weightedOperator_pow_le_finite_cost θ _
    (fun i => (hθ01 i).1) (fun i => (sq_nonneg _).trans (hC _)) hθsum I n

end Invariant233

namespace Invariant233

theorem product_phase_ranges {ι : Type*} [Countable ι]
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (J : ℕ → Finset ι) (K G : ℕ → ℝ)
    (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hblock : ∀ j, ∀ i ∈ J j, S i = ((J j).card : ℝ) * K j) :
    (∀ (j : ℕ) (θ : ι → ℝ),
      (∀ i ∈ J j, θ i ∈ Set.Icc (1 / (((J j).card : ℝ) * K j))
        (2 / (((J j).card : ℝ) * K j))) →
      ProductPhases.smallPhaseCondition (J j) (K j) (G j) θ) ∧
    (∀ᵐ θ ∂Measure.infinitePi
      (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
      (∀ j, ProductPhases.smallPhaseCondition (J j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop,
        ProductPhases.largePhaseCondition (J j) (((J j).card : ℝ) * K j) θ)) := by
  constructor
  · intro j θ hθ
    have hJ : 0 < (J j).card :=
      lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
    exact ProductPhases.smallPhaseCondition_of_bounds (J j) hJ (hK j) (hG j) θ hθ
  · exact ProductPhases.uniformProduct_ae_phaseRanges S hS J K G hK hG hgrowth hblock

end Invariant233

namespace Invariant233
open MeasureTheory Filter
open scoped Topology ENNReal

theorem compact_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hfirst : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.snd))
    (B : ℝ) (hB : 0 < B)
    (hcapn : ∀ i k, ∀ᵐ t ∂(νs i : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hcap : ∀ k, ∀ᵐ t ∂(ν : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0 :=
  CompactTransfer.compact_operator_transfer μ p hp F hF hFm hpm hν
    hfirst hsecond B hB hcapn hcap hzero

end Invariant233

namespace Invariant233

theorem scalar_sampling_estimates : ScalarSampling.ScalarSamplingEstimates :=
  ScalarRectangles.full_scalar_estimates

end Invariant233

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace Invariant233
open PositiveDiagonalModel
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
theorem positive_diagonal
    [IsProbabilityMeasure μ] (σ : Y ≃ᵐ Y) (hσ : Ergodic σ μ)
    (M : VonNeumannAlgebra (Space μ))
    (_htrace : IsFaithfulTracialVector M (Lp.const 2 μ e0))
    (hfields : ∀ A : Space μ →L[ℂ] Space μ, A ∈ M →
      ∃ a : Y → Fiber →L[ℂ] Fiber,
        (∀ y, ‖a y‖ ≤ ‖A‖) ∧
        (∀ v, StronglyMeasurable fun y => a y v) ∧
        (∀ ξ : Space μ, A ξ =ᵐ[μ] fun y => a y (ξ y)) ∧
        (∀ᵐ y ∂μ, a y * fiberShift = fiberShift * a (σ y)))
    (f : Lp ℝ ∞ μ) (hpositive : ∀ᵐ y ∂μ, 0 < f y)
    (P : Space μ →L[ℂ] Space μ) (hPm : P ∈ M) (hP : IsStarProjection P)
    (hinv : (1 - P) * lpOrbitWeightedShift σ f * P = 0)
    (htrace0 : 0 < diagonalState P) (htrace1 : diagonalState P < 1) :
    ∃ p : Y → Fiber →L[ℂ] Fiber,
      (∀ y, ‖p y‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun y => p y v) ∧
      (∀ ξ : Space μ, P ξ =ᵐ[μ] fun y => p y (ξ y)) ∧
      (∀ᵐ y ∂μ, IsStarProjection (p y)) ∧
      (∀ᵐ y ∂μ, p y * fiberShift = fiberShift * p (σ y)) ∧
      diagonalState P = ∫ y, (inner ℂ e0 (p y e0)).re ∂μ ∧
      (∀ᵐ y ∂μ, 0 < (inner ℂ e0 (p y e0)).re ∧
        (inner ℂ e0 (p y e0)).re < 1) :=
  PositiveDiagonalModel.positive_diagonal_in_algebra σ hσ M _htrace hfields
    f hpositive P hPm hP hinv htrace0 htrace1

end Invariant233

namespace Invariant233

theorem product_ordinary_tail_projection (θ c : ℕ → ℝ) (m : ℤ) :
    IsStarProjection (WeightedShift.fieldTailProjection (μ := ProductModel.baseMeasure) m) ∧
      WeightedShift.fieldTailProjection (μ := ProductModel.baseMeasure) m ≠ 0 ∧
      WeightedShift.fieldTailProjection (μ := ProductModel.baseMeasure) m ≠ 1 ∧
      (1 - WeightedShift.fieldTailProjection (μ := ProductModel.baseMeasure) m) *
        ProductModel.weightedOperator θ c *
        WeightedShift.fieldTailProjection (μ := ProductModel.baseMeasure) m = 0 ∧
      WeightedShift.fieldTailProjection (μ := ProductModel.baseMeasure) m ∉
        ProductModel.factor θ ∧
      (∀ ξ : ProductModel.Hilbert,
        ξ ∈ WeightedShift.fieldTailSubspace ProductModel.baseMeasure m ↔
          ∀ᵐ x ∂ProductModel.baseMeasure, ξ x ∈
            (Submodule.span ℂ ((fun k : ℤ =>
              (lp.single 2 k (1 : ℂ) : WeightedShift.Hilbert)) ''
                Set.Ici m)).topologicalClosure) :=
  by
  obtain ⟨hp, hzero, hone, hinv, hmem⟩ := ProductModel.ordinary_tail_projection θ c m
  exact ⟨hp, hzero, hone, hinv, hmem,
    fun ξ => WeightedShift.mem_fieldTailSubspace_iff_closedSpan m ξ⟩

theorem product_polar_structure (θ c : ℕ → ℝ)
    (h : ProductModel.AdmissibleAnglesAndCosts θ c)
    (hlog : HasNegInfiniteLogIntegral ProductModel.baseMeasure (ProductModel.weight θ c)) :
    ProductPolarStructure ProductModel.shiftOperator (ProductModel.weightedOperator θ c) :=
  ProductModel.productPolarStructure_of_negInfiniteLogIntegral θ c h hlog

end Invariant233

namespace Invariant233.Results

theorem rotation_factor_structure (θ : ℝ)
    (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (hθ : Irrational θ) :
    IsTypeII1FactorWithVector (Rotation.algebra θ) Rotation.vacuum ∧
      HasSeparablePredual (Rotation.algebra θ) :=
  Rotation.factor_structure θ hθ

end Invariant233.Results
namespace Invariant233

theorem conditional_labels {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) :
    ∃ hr : ∀ i, 0 < MixedRadix.radices p.q i,
      CircleCoupling.ConditionalLabelLaws p j hr := CircleCoupling.exists_conditionalLabelLaws hp j

theorem product_coupling_marginals
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) :
    OrderedProductCoupling.SourceMarginalProperties
      (OrderedProductCoupling.sourceBlocks m a b hm ha ha' hb hb' e tag)
      (OrderedProductCoupling.blockDensityBound OrderedProductCoupling.sourceKappa) :=
  OrderedProductCoupling.source_coupling_marginals m a b hm ha ha' hb hb' e tag

end Invariant233

namespace Invariant233

theorem truncation_bound {θ : ℝ} (_hθ0 : 0 < θ) (_hθ1 : θ < 1)
    (hθ : Irrational θ) {p : CircleParameterData} (hp : CircleParameterLaws θ p)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (htrace0 : 0 < (Rotation.vacuumFunctional P).re)
    (htrace1 : (Rotation.vacuumFunctional P).re < 1)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ hr : ∀ i, 0 < MixedRadix.radices p.q i,
      ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
        (∀ x, IsStarProjection (F x)) ∧
        (∀ x, ‖F x‖ ≤ ‖P‖) ∧
        (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
        (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
        p.RationalGraphIdentities θ F ∧
        CircleCoupling.TruncationBounds θ p hr F := by
  exact CircleParameterLaws.exists_rational_graph_field_with_truncation_bounds
    hθ hp hmem hP htrace0 htrace1 hinv

theorem digit_marginals {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) :
    ∃ hr : ∀ i, 0 < MixedRadix.radices p.q i,
      CircleCoupling.DigitMarginalLaws p hr := CircleCoupling.exists_digitMarginalLaws hp

end Invariant233

namespace Invariant233

theorem ordered_couplings {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ (hr : ∀ i, 0 < MixedRadix.radices p.q i)
      (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber),
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      CircleCoupling.OrderedCouplingIdentities p θ hr F := by
  exact CircleCoupling.exists_ordered_coupling_field hp hmem hP hT

end Invariant233

namespace Invariant233

theorem tail_attenuation {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) (hj : 1 ≤ j) :
    ∃ hr : ∀ i, 0 < MixedRadix.radices p.q i,
      CircleCoupling.TailAttenuation θ p j hr := by
  exact CircleCoupling.exists_actual_tail_attenuation hp j hj

end Invariant233

namespace Invariant233

theorem product_factor (θ : ℕ → ℝ)
    (hθ : ProductModel.JointlyRationallyIndependent θ) :
    IsTypeII1FactorWithVector (ProductModel.factor θ) ProductModel.traceVector ∧
      HasSeparablePredual (ProductModel.factor θ) ∧
      (∀ A : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert,
        A ∈ ProductModel.factor θ ↔
          ∃ (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
            (B : ℝ), ProductModel.IsCovariantFieldRepresentation θ A F B) ∧
      (∀ (A : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert)
        (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber) (B : ℝ),
        ProductModel.IsCovariantFieldRepresentation θ A F B →
          vectorTrace ProductModel.traceVector A = ProductModel.centralDiagonalIntegral F) := by
  exact ProductModel.factor_complete θ hθ
end Invariant233

namespace Invariant233

theorem affiliated_transport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (M : VonNeumannAlgebra E) (τ : TracialState M)
    (hτ : IsNormalFaithfulTracialState M τ)
    (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H) (hpos : IsPositivePartial H)
    (hinj : Function.Injective H) (haff : IsAffiliated M H)
    (A B : M)
    (hD : ∀ x : H.domain, (A : E →L[ℂ] E) (x : E) ∈ H.domain)
    (hinter : ∀ x : H.domain,
      H ⟨(A : E →L[ℂ] E) (x : E), hD x⟩ = (B : E →L[ℂ] E) (H x))
    (p : M) (hp : IsStarProjection (p : E →L[ℂ] E))
    (hinv : (1 - (p : E →L[ℂ] E)) * (A : E →L[ℂ] E) * (p : E →L[ℂ] E) = 0) :
    ∃ P : M,
      (P : E →L[ℂ] E) =
        (InvariantRotation.AffiliatedTransport.transported H
          (p : E →L[ℂ] E).range).starProjection ∧
      IsStarProjection (P : E →L[ℂ] E) ∧
      (1 - (P : E →L[ℂ] E)) * (B : E →L[ℂ] E) * (P : E →L[ℂ] E) = 0 ∧
      τ P = τ p := by
  exact affiliated_transport_proof M τ hτ H hH hpos hinj haff A B hD hinter p hp hinv

end Invariant233

namespace Invariant233.Results

section PrincipalHilbertConsequences
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem transitive_commutant_on_separable_hilbert
    [TopologicalSpace.SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H) :
    ∃ T : H →L[ℂ] H, T ≠ 0 ∧ NormQuasinilpotent T ∧
      HasNoNontrivialHyperinvariantSubspace T ∧
      operatorCommutant T ≠ ⊤ ∧ IsStronglyClosed (operatorCommutant T) ∧
      IsTransitive (operatorCommutant T) := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hθ0 : 0 < Real.sqrt 2 - 1 := by nlinarith
  have hθ1 : Real.sqrt 2 - 1 < 1 := by nlinarith
  have hθ : Irrational (Real.sqrt 2 - 1) := by
    simpa using irrational_sqrt_two.sub_intCast 1
  obtain ⟨f, _hf, hmem, hproj, hne, hqn, _hdet⟩ :=
    prescribed_irrational_counterexample (Real.sqrt 2 - 1) hθ0 hθ1 hθ
  exact Invariant233.transitive_commutant_of_circle_witness hH
    (Rotation.algebra (Real.sqrt 2 - 1)) hmem hne hqn hproj

theorem cho_ko_lee_comparison [TopologicalSpace.SeparableSpace H]
    (hH : ¬ FiniteDimensional ℂ H) :
    ∃ T : H →L[ℂ] H, T ≠ 0 ∧ NormQuasinilpotent T ∧
      HasNoNontrivialHyperinvariantSubspace T ∧
      operatorCommutant (1 + T) = operatorCommutant T ∧
      ∀ C : H → H, ∀ hC : IsConjugation C,
        IsInfiniteConjugationIsometry hC.toHilbertConjugation (1 + T) ∧
        HasNoNontrivialHyperinvariantSubspace (1 + T) := by
  obtain ⟨T, hne, hqn, hhyper, _hproper, _hclosed, _htrans⟩ :=
    transitive_commutant_on_separable_hilbert hH
  exact Invariant233.cho_ko_lee_complete_comparison_of_exists ⟨T, hne, hqn, hhyper⟩

end PrincipalHilbertConsequences
end Invariant233.Results

namespace Invariant233
theorem product_pair_identity (θ c : ℕ → ℝ)
    (_hθ : ProductModel.JointlyRationallyIndependent θ)
    (hθ01 : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1) (hθsum : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (hsampling : ProductModel.HasAllFiniteCoordinateSampling θ)
    (p : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert)
    (hpM : p ∈ ProductModel.factor θ) (hp : IsStarProjection p)
    (hinv : (1 - p) * ProductModel.weightedOperator θ c * p = 0) :
    ∃ F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber,
      ProductModel.IsCovariantFieldRepresentation θ p F 1 ∧
      (∀ x, IsStarProjection (F x)) ∧
      ∀ I : Finset ℕ, ∀ᵐ xy ∂ProductModel.triangularLaw I,
        ProductModel.PairIdentity θ c F xy := by
  exact ProductModel.exists_covariantProjectionField_pairIdentity θ c
    (fun i => (hθ01 i).1) hθsum hc hsampling p hpM hp hinv
end Invariant233

namespace Invariant233

theorem product_biased_identity (θ c : ℕ → ℝ)
    (_hθ : ProductModel.JointlyRationallyIndependent θ)
    (hθ01 : ∀ i, θ i ∈ Set.Ico (0 : ℝ) 1) (hθsum : Summable θ)
    (hc : ∀ i, 0 ≤ c i) (hsampling : ProductModel.HasAllFiniteCoordinateSampling θ)
    (P : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert)
    (hPM : P ∈ ProductModel.factor θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * ProductModel.weightedOperator θ c * P = 0)
    (m : ℕ → ℕ) (a b : ℕ → ℝ) (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) :
    ∃ F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber,
      ProductModel.IsCovariantFieldRepresentation θ P F 1 ∧
      (∀ x, IsStarProjection (F x)) ∧
      ∀ tag : ℕ, ∀ᵐ xy ∂OrderedProductCoupling.circlePairLaw
        (OrderedProductCoupling.sourceBlocks m a b hm ha ha' hb hb' e tag),
        ProductModel.PairIdentity θ c F xy := by
  exact OrderedProductCoupling.exists_source_covariantProjectionField_biased_pairIdentity
    θ c (fun i => (hθ01 i).1) hθsum hc hsampling P hPM hP hinv
    m a b hm ha ha' hb hb' e

end Invariant233

namespace Invariant233

theorem measurable_counterexample (θ : ℝ)
    (_hθ0 : 0 < θ) (_hθ1 : θ < 1) (hθ : Irrational θ)
    (p : CircleParameterData) (hp : CircleParameterLaws θ p) :
    p.measurableOperator θ hp ∈ Rotation.algebra θ ∧
      ∀ P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert,
        P ∈ Rotation.algebra θ → IsStarProjection P →
        0 < (Rotation.vacuumFunctional P).re →
        (Rotation.vacuumFunctional P).re < 1 →
        (1 - P) * p.measurableOperator θ hp * P ≠ 0 := by
  refine ⟨hp.measurableOperator_mem_algebra, ?_⟩
  intro P hmem hP htrace0 htrace1 hinv
  rcases hp.measurableOperator_hasOnlyTrivialInvariantProjections hθ P hmem hP hinv with h0 | h1
  · subst P
    simp [Rotation.vacuumFunctional] at htrace0
  · subst P
    simp [Rotation.vacuumFunctional_one] at htrace1

end Invariant233

namespace Invariant233

theorem product_finite_coordinate_sampling
    (p : ProductScaleData) (hp : ProductScaleLaws p)
    (S : ℕ → ℝ) (hS : ∀ i, 0 < S i)
    (hblock : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      S i = (p.m j : ℝ) * p.K j) :
    ∀ᵐ θ ∂Measure.infinitePi (fun i =>
      ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
      ProductModel.HasAllFiniteCoordinateSampling θ := by
  exact ProductModel.SamplingWeights.ae_hasAllFiniteCoordinateSampling hp S hS hblock

end Invariant233
end

namespace Invariant233

local instance ProductModel.instFactOneLeTwoCounterexample :
    Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

abbrev ProductModel.CounterexampleFiber : Type :=
  @lp ℤ (fun _ => ℂ) (fun _ => Complex.instNormedAddCommGroup) 2

abbrev ProductModel.CounterexampleHilbert : Type :=
  @MeasureTheory.Lp ProductModel.Base ProductModel.CounterexampleFiber MeasurableSpace.pi
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) ProductModel.instFactOneLeTwoCounterexample)
    2 ProductModel.baseMeasure

instance ProductModel.instCompleteSpaceHilbertCounterexample :
    CompleteSpace ProductModel.CounterexampleHilbert := inferInstance

def ProductOperatorProperties {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (factor : VonNeumannAlgebra H)
    (traceVector : H) (shift operator : H →L[ℂ] H) : Prop :=
  IsTypeII1FactorWithVector factor traceVector ∧
    HasSeparablePredual factor ∧
    operator ∈ factor ∧ operator ≠ 0 ∧
    NormQuasinilpotent operator ∧
    vectorFugledeKadisonDeterminant traceVector operator = 0 ∧
    spectrum ℂ operator = {0} ∧
    IsVectorBrownMeasure traceVector operator (MeasureTheory.Measure.dirac 0) ∧
    HasOnlyTrivialInvariantProjections factor operator ∧
    ProductPolarStructure shift operator

@[instance_reducible]
noncomputable def ProductModel.counterexampleHilbertNormedAddCommGroup :
    NormedAddCommGroup ProductModel.CounterexampleHilbert :=
  @MeasureTheory.Lp.instNormedAddCommGroup ProductModel.Base ProductModel.CounterexampleFiber
    MeasurableSpace.pi 2 ProductModel.baseMeasure
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) ProductModel.instFactOneLeTwoCounterexample)
    ProductModel.instFactOneLeTwoCounterexample

@[instance_reducible]
noncomputable def ProductModel.counterexampleHilbertInnerProductSpace :
    @InnerProductSpace ℂ ProductModel.CounterexampleHilbert Complex.instRCLike
      ProductModel.counterexampleHilbertNormedAddCommGroup.toSeminormedAddCommGroup :=
  @MeasureTheory.L2.innerProductSpace ProductModel.Base ProductModel.CounterexampleFiber ℂ
    Complex.instRCLike MeasurableSpace.pi ProductModel.baseMeasure
    (@lp.normedAddCommGroup ℤ (fun _ => ℂ) 2
      (fun _ => Complex.instNormedAddCommGroup) ProductModel.instFactOneLeTwoCounterexample)
    (@lp.instInnerProductSpace ℤ ℂ Complex.instRCLike (fun _ => ℂ)
      (fun _ => Complex.instNormedAddCommGroup)
      (fun _ => @RCLike.innerProductSpace ℂ Complex.instRCLike))

def ProductModel.HasCounterexampleOperator (θ c : ℕ → ℝ) : Prop :=
  @ProductOperatorProperties ProductModel.CounterexampleHilbert
    ProductModel.counterexampleHilbertNormedAddCommGroup
    ProductModel.counterexampleHilbertInnerProductSpace
    ProductModel.instCompleteSpaceHilbertCounterexample (ProductModel.factor θ)
    ProductModel.traceVector ProductModel.shiftOperator (ProductModel.weightedOperator θ c)

def ProductModel.IsCounterexampleRealization (θ c : ℕ → ℝ) : Prop :=
  ProductModel.AdmissibleAnglesAndCosts θ c ∧
    ProductModel.HasAllFiniteCoordinateSampling θ ∧
    Filter.Eventually (fun x : ProductModel.Base => 0 < ProductModel.weight θ c x)
      (@MeasureTheory.ae ProductModel.Base
        (@MeasureTheory.Measure ProductModel.Base MeasurableSpace.pi)
        MeasureTheory.Measure.instFunLike MeasureTheory.Measure.instOuterMeasureClass
        ProductModel.baseMeasure) ∧
    @HasNegInfiniteLogIntegral ProductModel.Base MeasurableSpace.pi
      ProductModel.baseMeasure (ProductModel.weight θ c) ∧
    ProductModel.HasCounterexampleOperator θ c

namespace Results

theorem product_realization :
    ∃ θ c : ℕ → ℝ, ProductModel.IsCounterexampleRealization θ c := by
  exact ProductModel.product_realization_of_ae_sampling Invariant233.product_finite_coordinate_sampling

end Results
end Invariant233

end OAI
