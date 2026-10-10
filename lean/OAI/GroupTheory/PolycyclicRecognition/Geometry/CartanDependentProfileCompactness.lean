import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProfileCompactness

namespace OAI

/-! # Compact profile families with scale-dependent parameter sets -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology NNReal

variable {EG G I W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  [Fintype I] [DecidableEq I]

include T in
/-- The permitted boxes may depend on the scale. Their profiles still lie
in one compact family; independent choices at the other scales supply an
ordinary parameter family for the established compactness theorem. -/
theorem exists_compact_dependent_cartan_profiles
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (X : I → H) {k : ℕ} (hk : lowerCentralSeries ℝ H H k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) β.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hnonneg : ∀ i, 0 ≤ scale i)
    {A : ℕ → Type*} [∀ n, Nonempty (A n)]
    {K : ℝ≥0} (J : ∀ n, A n → G → W) (hJ : ∀ n u, LipschitzWith K (J n u))
    (x suffix : ∀ n, A n → G) (B : ℝ)
    (hsuffix : ∀ n u, dist 1 (suffix n u) / Real.exp (scale n) ≤ B) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    let φ := fun n z => F.inclusionD (F.ExpD (F.D.equiv
      ((exponentialRescaleBasis b cost (scale n)).equivFun.symm z)))
    ∃ S : Set C((Fin (finrank ℝ H) → ℝ), W), IsCompact S ∧ ∀ n u,
      ∃ f ∈ S, ∀ z, f z = rescaledMapProfile (J n u) (x n u) (suffix n u) (scale n) (φ n) z := by
  classical
  dsimp only
  obtain ⟨S, hS, hmem⟩ := exists_compact_cartan_profiles T F hExpG realize haarD dynkinD
    X hk hletters b₀ β hβ scale hscale hnonneg
    (fun n (u : ∀ n, A n) => J n (u n)) (fun n u => hJ n (u n))
    (fun n u => x n (u n)) (fun n u => suffix n (u n)) B
    (fun n u => hsuffix n (u n))
  refine ⟨S, hS, ?_⟩
  intro n u
  let choices : ∀ n, A n := fun n => Classical.choice (inferInstance : Nonempty (A n))
  simpa only [Function.update_self] using hmem n (Function.update choices n u)

end PolycyclicRecognition

end

end OAI
