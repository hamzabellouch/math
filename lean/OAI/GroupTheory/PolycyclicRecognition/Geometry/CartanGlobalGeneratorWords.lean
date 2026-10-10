import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GlobalGeneratorWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds

namespace OAI

/-! # Bounded generator word width of the whole Cartan nilpotent factor

Uniform rescaled generation has a fixed word-length bound. Letting all
positive widths grow exhausts the Lie algebra; absorbing the scale into
the unrestricted real amplitudes gives the same bound globally.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
/-- Uniform Cartan box generation gives a global bound for exponential words. -/
theorem exists_global_cartan_generator_words_lie
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ N : ℕ, ∀ v : cartanRootIdeal H, ∃ u : List (Fin M.letterCount × ℝ),
      u.length ≤ N ∧ generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) u =
        F.ExpN (F.N.equiv v) := by
  exact global_generator_words_of_all_rescalings M.letter (F.ExpN ∘ F.N.equiv)
    M.wordList b₀ (M.exists_uniform_cartan_rescaled_generator_words
      T F hExpG realize haarN dynkinN b₀ 1)

include T in
/-- A single finite number of homogeneous generator exponentials suffices
for every element, with unrestricted real amplitudes. -/
theorem exists_global_cartan_generator_words
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H)) :
    ∃ N : ℕ, ∀ n : F.N.carrier, ∃ u : List (Fin M.letterCount × ℝ),
      u.length ≤ N ∧ generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) u = n := by
  obtain ⟨N, hw⟩ := M.exists_global_cartan_generator_words_lie T F hExpG realize haarN dynkinN b₀
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hsurj : Function.Surjective (F.ExpN ∘ F.N.equiv) :=
    ((funext hchartN ▸ chartN.bijective).comp F.N.equiv.bijective).surjective
  refine ⟨N, ?_⟩
  intro n
  obtain ⟨v, hv⟩ := hsurj n
  obtain ⟨u, hu, he⟩ := hw v
  exact ⟨u, hu, he.trans hv⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
