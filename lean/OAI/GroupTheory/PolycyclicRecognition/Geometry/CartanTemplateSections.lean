import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanInverseSections
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledInverseSections
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TemplateSupportDirections

namespace OAI

/-! # Continuous inverse schemes in actual Cartan boxes

The same published exponential and Dynkin inputs now supply a uniformly
bounded continuous endpoint coding on a fixed ball in every actual
rescaled Cartan root-ideal chart.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- Common continuous endpoint coding for all actual Cartan rescalings. -/
theorem exists_uniform_template_inverse_sections
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (v : Fin M.letterCount → H) :
    ∃ (ε : ℝ) (N : ℕ) (C : ℝ), 0 < ε ∧ 1 ≤ C ∧
      ∀ (β : M.Bases),
        IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
          (fun w => bracketWordExponent (M.templateSupportExponent v) w) β.val →
        ∀ r : ℝ, 0 ≤ r →
        let b := exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
          (fun j => bracketWordExponent (M.templateSupportExponent v) (β.val j)) r
        ∃ (w : Fin (finrank ℝ (cartanRootIdeal H)) → List (Fin M.letterCount × ℝ))
          (i : Fin (finrank ℝ (cartanRootIdeal H)) → Fin M.letterCount)
          (σ : (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) →
            Fin (finrank ℝ (cartanRootIdeal H)) → ℝ),
          ContinuousOn σ (ball 0 ε) ∧ ∀ y ∈ ball (0 : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) ε,
            ‖σ y‖ < 1 ∧ (generatorSchemeWord w i (σ y)).length ≤ N ∧
            (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
            generatorGroupWord (fun i => Real.exp (r * M.templateSupportExponent v i) • M.letter i)
              (F.ExpN ∘ F.N.equiv) (generatorSchemeWord w i (σ y)) =
                F.ExpN (F.N.equiv (b.equivFun.symm y)) := by
  obtain ⟨ε, N, C, hε, hC, hcode⟩ := M.exists_uniform_cartan_inverse_sections T F
    hExpG realize haarN dynkinN b₀
  exact ⟨ε, N, C, hε, hC, fun β hβ r hr =>
    hcode (M.templateSupportExponent v) β hβ r hr⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
