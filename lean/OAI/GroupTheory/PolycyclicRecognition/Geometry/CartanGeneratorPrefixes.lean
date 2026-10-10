import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledWordPrefixes

namespace OAI

/-! # Generator words with all Cartan prefixes controlled -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieModule
open scoped Manifold

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- The words supplied by uniform generation also have uniformly bounded
logarithmic prefixes in the same maximizing rescaled basis. -/
theorem exists_uniform_cartan_generator_prefixes
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (R : ℝ) :
    ∃ (N : ℕ) (C D : ℝ), 1 ≤ C ∧ 0 ≤ D ∧
      ∀ (s : Fin M.letterCount → ℝ) (β : M.Bases),
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ v : cartanRootIdeal H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun k => bracketWordExponent s (β.val k)) r).equivFun v‖ ≤ R →
      ∃ u : List (Fin M.letterCount × ℝ), u.length ≤ N ∧ (∀ z ∈ u, |z.2| ≤ C) ∧
        generatorGroupWord (fun i => Real.exp (r * s i) • M.letter i)
          (F.ExpN ∘ F.N.equiv) u = F.ExpN (F.N.equiv v) ∧
        ∀ j : ℕ, ∃ w : cartanRootIdeal H,
          F.ExpN (F.N.equiv w) =
            generatorGroupWord (fun i => Real.exp (r * s i) • M.letter i)
              (F.ExpN ∘ F.N.equiv) (u.take j) ∧
          ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
            (fun k => bracketWordExponent s (β.val k)) r).equivFun w‖ ≤ D := by
  obtain ⟨N, C, hC, hwords⟩ := M.exists_uniform_cartan_rescaled_generator_words T F
    hExpG realize haarN dynkinN b₀ R
  obtain ⟨D, hD, hprefix⟩ := exists_uniform_rescaled_word_prefix_bound dynkinN
    F.N.equiv F.ExpN F.isExpN M.letter M.bound_zero M.letter_mem_wordList b₀ N
    ((by norm_num : (0 : ℝ) ≤ 1).trans hC)
  refine ⟨N, C, D, hC, hD, ?_⟩
  intro s β hβ r hr v hv
  obtain ⟨u, hu, hamp, hend⟩ := hwords s β hβ r hr v hv
  exact ⟨u, hu, hamp, hend, fun j => hprefix s β hβ r hr u hu hamp j⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
