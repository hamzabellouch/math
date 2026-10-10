import OAI.GroupTheory.PolycyclicRecognition.Analysis.GradedHaar
import OAI.GroupTheory.PolycyclicRecognition.Geometry.GradedHeight
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RescaledFlowLipschitz
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDProfiles

namespace OAI

/-! # The actual graded Cartan group's geometric data -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter MeasureTheory
open scoped Manifold Topology NNReal Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G W I A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
omit [IsIsometricSMul G G] in
/-- The conjugation identity for the actual graded Cartan law is derived
from the published faithful realization and the original exponential. -/
theorem cartan_graded_conjugation
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    {n c : ℕ} (b : Basis (Fin n) ℝ H) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (coeff : DynkinCoefficients c 2)
    (hm : ∀ x y, F.ExpD (finiteDynkinPolynomial coeff ![x, y]) = F.ExpD x * F.ExpD y) :
    ExponentialConjugationLaw (dynkinProduct coeff (gradedCoordinateBracket b cost))
      (gradedCoordinateBracket b cost) := by
  obtain ⟨d, hd, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin d) (Fin d) ℝ)ˣ =>
      (u : Matrix (Fin d) (Fin d) ℝ)) he)
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := haarD.2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hinj : Function.Injective (F.ExpD ∘ F.D.equiv) :=
    ((funext hchartD ▸ chartD.bijective).comp F.D.equiv.bijective).injective
  exact graded_exponentialConjugationLaw b cost hweight (F.ExpD ∘ F.D.equiv) hinj
    (fun x => by simp [F.isExpD.map_neg]) coeff
    (model_binary_dynkin F.D.equiv F.ExpD coeff hm) (j.comp H.incl)
    (ρ.comp F.inclusionD) (hρ.comp F.closedD.injective) (fun x => by
      change ρ (F.inclusionD (F.ExpD (F.D.equiv x))) = _
      rw [F.compatibleD, hmatch]
      rfl)

variable [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I] [DecidableEq I]
  [MeasurableSpace A]

include T in
/-- Supported actual Cartan profiles have one horizontal Lipschitz bound
for each direction, uniform in the starting point and supported profile. -/
theorem lipschitz_supported_cartan_profiles
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
    (hactual : ∀ i u z, (profile i u).val z =
      rescaledMapProfile (J i u) (x i u) (suffix i u) (scale i)
        (fun z => F.inclusionD (F.ExpD (F.D.equiv
          ((exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords d) β)
            (fun j => bracketWordExponent (fun _ : I => 1) (β.val j)) (scale i)).equivFun.symm z)))) z) :
    let b := WordBasisSelections.basis X (boundedBracketWords d) β
    let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
    ∀ v : H, ∃ C : ℝ≥0, ∀ f : S, f ∈ (ν : Measure S).support → ∀ z,
      LipschitzWith C (fun t : ℝ => f.val
        (dynkinFlowMap coeff (gradedCoordinateBracket b cost) (gradedGenerator b cost 1 v) (z, t))) := by
  dsimp only
  intro v
  let b := WordBasisSelections.basis X (boundedBracketWords d) β
  let cost := fun j => bracketWordExponent (fun _ : I => 1) (β.val j)
  have hv : ∀ j, b.repr v j ≠ 0 → (1 : ℝ) ≤ cost j := by
    intro j _
    have hlen (w : FreeMagma I) : 1 ≤ bracketWordLength w := by
      induction w using FreeMagma.rec with
      | of i => simp [bracketWordLength]
      | mul u w hu hw => simp only [bracketWordLength]; omega
    dsimp [cost]
    rw [bracketWordExponent_one]
    exact_mod_cast hlen (β.val j)
  apply lipschitz_supported_rescaled_flow (F.ExpD ∘ F.D.equiv) F.inclusionD b cost
    (maximizing_word_basis_bracket_weight X hDnil bD₀ (fun _ => 1) β hβ)
    coeff (model_binary_dynkin F.D.equiv F.ExpD coeff hm) v hv
    ?_ ?_ ?_ scale hscale J hJ x suffix S hS samples profile hp ν hν hactual
  · simpa only [Function.comp_apply, F.compatibleD, SetLike.val_smul] using
      continuous_exp_line_of_published_realization T ExpG hExpG realize v
  · simp [F.isExpD.map_zero]
  · intro s t
    simp only [Function.comp_apply, map_smul, F.isExpD.map_add_smul, map_mul]

end PolycyclicRecognition

end

end OAI
