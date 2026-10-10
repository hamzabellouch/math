import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRootCocycle
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LogarithmicCocycleWords
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolynomialBoxWords

namespace OAI

/-! # Uniform sublinearity on the actual finite Cartan root words -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule
open scoped Manifold

attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (M : CartanWordModel H) (hExpG : IsGroupExponential ExpG)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (hρ : ∀ v, Continuous (fun g => ρ g v))
  (hfix : ∀ v, (∀ g, ρ g v = v) → v = 0)

include T M hExpG realize haarN dynkinN hρ hfix in
theorem cartan_generator_cocycle_sublinear_log
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    (i : Fin M.letterCount) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ,
      ‖b (F.inclusionN (F.ExpN (F.N.equiv (t • M.letter i))))‖ ≤
        ε * Real.log (2 + |t|) + B := by
  let v : rootSpace H (M.weight i) := ⟨M.letter i, M.letter_root i⟩
  have hroot := cartan_root_cocycle_sublinear_log T F M hExpG realize haarN dynkinN
    ρ hρ hfix b hbc hb (M.weight i) (M.weight_nonzero i)
  have hline := sublinear_log_along_smul (fun w : rootSpace H (M.weight i) => b (ExpG w)) hroot v
  simpa only [F.compatibleN, SetLike.val_smul, v] using hline

include T M hExpG realize haarN dynkinN hρ hfix in
theorem cartan_cocycle_bounded_root_words
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    (k p : ℕ) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ u : List (Fin M.letterCount × ℝ), u.length ≤ k →
      (∀ z ∈ u, |z.2| ≤ C * (1 + r) ^ p * Real.exp (r * c)) →
      ‖b (F.inclusionN (generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) u))‖ ≤
        ε * r + B := by
  have h := hb.sublinear_bounded_log_words
    (fun i t => F.inclusionN (F.ExpN (F.N.equiv (t • M.letter i))))
    (cartan_generator_cocycle_sublinear_log T F M hExpG realize haarN dynkinN ρ hρ hfix b hbc hb)
    k p hC hc
  simpa only [generatorGroupWord, map_list_prod, List.map_map, Function.comp_def] using h

include T M hExpG realize haarN dynkinN hρ hfix in
theorem cartan_cocycle_polynomial_boxes
    (b : G → E) (hbc : Continuous b) (hb : IsUnitaryCocycle ρ b)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 < s i) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent s w) β.val)
    {C : ℝ} (hC : 0 ≤ C) (p : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ v : cartanRootIdeal H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun v‖ ≤ C * (1 + r) ^ p →
      ‖b (F.inclusionN (F.ExpN (F.N.equiv v)))‖ ≤ ε * r + B := by
  obtain ⟨k, D, c, hD, hc, hwords⟩ := M.exists_polynomial_box_generator_words T F
    hExpG realize haarN dynkinN b₀ s hs β hβ hC p
  intro ε hε
  obtain ⟨B, hB, hbound⟩ := cartan_cocycle_bounded_root_words T F M hExpG realize haarN dynkinN
    ρ hρ hfix b hbc hb k 0 hD hc ε hε
  refine ⟨B, hB, fun r hr v hv => ?_⟩
  obtain ⟨u, hu, hamp, he⟩ := hwords r hr v hv
  have h := hbound r hr u hu (by simpa only [pow_zero, mul_one] using hamp)
  rw [he] at h
  exact h

end PolycyclicRecognition

end

end OAI
