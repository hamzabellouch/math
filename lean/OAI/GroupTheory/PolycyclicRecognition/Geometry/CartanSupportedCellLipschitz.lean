import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanGradedGeometry
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction

namespace OAI

/-! # Supported Cartan profile bounds use only samples in the carrying cell -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter MeasureTheory Set
open scoped Manifold Topology NNReal Matrix.Norms.Operator

variable {EG G W I A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

variable [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  [MeasurableSpace A]

include T in
theorem lipschitz_supported_cartan_profiles_on
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords d))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    {c : ℕ} (coeff : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpD (finiteDynkinPolynomial coeff ![x, y]) = F.ExpD x * F.ExpD y)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    {K : ℝ≥0} (J : ℕ → A → G → W) (hJ : ∀ n u, LipschitzWith K (J n u))
    (x suffix : ℕ → A → G)
    (S : Set C((Fin (finrank ℝ H) → ℝ), W)) (hS : IsCompact S)
    [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (samples : ℕ → ProbabilityMeasure A) (profile : ℕ → A → S)
    (hp : ∀ n, Measurable (profile n)) (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map (samples n) (profile n)) atTop (𝓝 ν))
    (C : Set A) (hC : MeasurableSet C)
    (hfull : ∀ n, ∀ᵐ a ∂(samples n : Measure A), a ∈ C)
    (hactual : ∀ i u, u ∈ C → ∀ z, (profile i u).val z =
      rescaledMapProfile (J i u) (x i u) (suffix i u) (scale i)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
            (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (scale i)).equivFun.symm z)))) z) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    ∀ v : H, ∃ C : ℝ≥0, ∀ f : S, f ∈ (ν : Measure S).support → ∀ z,
      LipschitzWith C (fun t : ℝ => f.val
        (dynkinFlowMap coeff (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))) := by
  let restricted := fun n => supportedProbabilityRestriction (samples n) C hC (hfull n)
  have hlim : Tendsto (fun n => ProbabilityMeasure.map (restricted n)
      (fun a : C => profile n a.val)) atTop (𝓝 ν) := by
    simpa only [restricted, map_supportedProbabilityRestriction _ _ _ _ _ (hp _)] using hν
  exact lipschitz_supported_cartan_profiles T F hExpG realize X hDnil bD₀ β hβ coeff hm
    scale hscale (fun n (a : C) => J n a.val) (fun n a => hJ n a.val)
    (fun n (a : C) => x n a.val) (fun n (a : C) => suffix n a.val) S hS restricted
    (fun n (a : C) => profile n a.val)
    (fun n => (hp n).comp measurable_subtype_coe) ν hlim
    (fun n a z => hactual n a.val a.property z)

end PolycyclicRecognition

end

end OAI
