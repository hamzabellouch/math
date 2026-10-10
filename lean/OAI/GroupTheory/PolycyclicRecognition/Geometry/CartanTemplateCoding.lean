import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateSections
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTemplateWordPath

namespace OAI

/-! # Continuous endpoint families in actual template boxes

A common coordinate ball parametrizes true endpoints in every maximizing
rescaled box. The chosen support paths have continuous time samples and
uniform bounds, so coordinates can be sampled independently of normalized
quasi-isometry pairs.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

include T in
/-- Actual segment-box endpoints have continuously sampled paths on a
common positive-radius coordinate ball, with uniform coarse metric bounds. -/
theorem exists_continuous_template_box_paths
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) (v : Fin M.letterCount → H)
    (E : Set W) (hE : Convex ℝ E) (hE0 : (0 : W) ∈ E)
    (hvE : ∀ i, (l (Exp (v i))).toAdd ∈ E) :
    ∃ (ε C : ℝ), 0 < ε ∧ 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ β : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
      let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
      ∃ γ : ∀ y : ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε,
          Path (1 : G) (F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val)))),
        (∀ t, Continuous (fun y => γ y t)) ∧
        (∀ y, PathMetricBound (γ y) (C * r) (C * (1 + Real.log (2 + r)))) ∧
        ∀ y t, ∃ z ∈ E, (l (γ y t)).toAdd = r • z := by
  classical
  obtain ⟨ε, N, B, hε, hB, hcode⟩ :=
    M.exists_uniform_template_inverse_sections T F hExp realize haarN dynkinN b₀ v
  obtain ⟨C, hC, hpath⟩ := M.exists_templateWordPath_bound T hExp realize l hl hL hbound
    v E hE hE0 hvE (by linarith : 0 ≤ B) N
  refine ⟨ε, C, hε, hC, ?_⟩
  intro r hr β hβ b
  have hsection := hcode β hβ r hr
  dsimp only at hsection
  rcases hsection with ⟨w, i, σ, hσ, hs⟩
  let Y := ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε
  let σ' : Y → Fin (finrank ℝ (cartanRootIdeal H)) → ℝ := fun y => σ y.val
  have hσ' : Continuous σ' := continuousOn_iff_continuous_domRestrict.mp hσ
  let u (y : Y) := generatorSchemeWord w i (σ' y)
  have hspec (y : Y) := hs y.val y.property
  have hend (y : Y) :
      F.inclusionN (F.ExpN (F.N.equiv (b.equivFun.symm y.val))) =
      ((M.templateScaledWord v r (u y)).map
        (fun q => Exp (q.2 • (M.letter q.1 : GroupLieAlgebra (𝓘(ℝ, EG)) G)))).prod := by
    exact ((M.templateScaledWord_product F v r (u y)).trans (congrArg F.inclusionN (hspec y).2.2.2)).symm
  let γ (y : Y) := (M.templateWordPath T hExp realize v r (u y)).cast rfl (hend y)
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro t
    exact M.continuous_templateWordPath_scheme T hExp realize v r w i σ' hσ' t
  · intro y
    exact ((hpath r hr (u y) (hspec y).2.1 (hspec y).2.2.1).1).cast rfl (hend y)
  · intro y t
    exact (hpath r hr (u y) (hspec y).2.1 (hspec y).2.2.1).2 t

end PolycyclicRecognition.CartanWordModel

end

end OAI
