import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformGeneration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialBoxAbsorption
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponentBounds

namespace OAI

/-! # Bounded root words for polynomially enlarged Cartan boxes

The polynomial radius is absorbed in an affine increase of the box scale.
The resulting root amplitudes have a uniform exponential bound.
-/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

include T in
theorem exists_polynomial_box_generator_words
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 < s i) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (fun w => bracketWordExponent s w) β.val)
    {C : ℝ} (hC : 0 ≤ C) (p : ℕ) :
    ∃ (k : ℕ) (D c : ℝ), 0 ≤ D ∧ 0 ≤ c ∧ ∀ r : ℝ, 0 ≤ r →
      ∀ v : cartanRootIdeal H,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis M.letter M.wordList β)
        (fun j => bracketWordExponent s (β.val j)) r).equivFun v‖ ≤ C * (1 + r) ^ p →
      ∃ u : List (Fin M.letterCount × ℝ), u.length ≤ k ∧
        (∀ z ∈ u, |z.2| ≤ D * Real.exp (r * c)) ∧
        generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) u = F.ExpN (F.N.equiv v) := by
  classical
  obtain ⟨k, U, hU, hgen⟩ := M.exists_uniform_cartan_rescaled_generator_words T F
    hExpG realize haarN dynkinN b₀ 1
  obtain ⟨lo, _, hlo, _, hcost⟩ := exists_positive_wordExponent_bounds s hs M.wordList
  obtain ⟨A, B, hA, hB, habsorb⟩ := exists_affine_scale_absorbing_polynomial
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => bracketWordExponent s (β.val j)) hlo (fun j => (hcost (β.val j)).1) hC p
  let S := ∑ i, s i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => (hs i).le)
  have hsi (i : Fin M.letterCount) : s i ≤ S :=
    Finset.single_le_sum (fun j _ => (hs j).le) (Finset.mem_univ i)
  refine ⟨k, U * Real.exp (B * S), A * S, by positivity, by positivity, ?_⟩
  intro r hr v hv
  have ht : 0 ≤ A * r + B := add_nonneg (mul_nonneg (by linarith) hr) hB
  obtain ⟨u, hu, hamp, he⟩ := hgen s β hβ (A * r + B) ht v (habsorb r hr v hv)
  let u' := u.map (fun z => (z.1, z.2 * Real.exp ((A * r + B) * s z.1)))
  refine ⟨u', by simpa only [u', List.length_map] using hu, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    change |w.2 * Real.exp ((A * r + B) * s w.1)| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp : (A * r + B) * s w.1 ≤ B * S + r * (A * S) := by
      have h := mul_le_mul_of_nonneg_left (hsi w.1) ht
      nlinarith
    calc
      _ ≤ U * Real.exp (B * S + r * (A * S)) :=
        mul_le_mul (hamp w hw) (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le (by linarith)
      _ = _ := by rw [Real.exp_add]; ring
  · have heq : generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) u' =
        generatorGroupWord (fun i => Real.exp ((A * r + B) * s i) • M.letter i)
          (F.ExpN ∘ F.N.equiv) u := by
      simp only [generatorGroupWord, u', List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro z _
      rw [smul_smul]
    exact heq.trans he

end PolycyclicRecognition.CartanWordModel

end

end OAI
