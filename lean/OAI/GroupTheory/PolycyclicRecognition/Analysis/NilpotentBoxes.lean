import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinInput
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedWordBrackets

namespace OAI

/-! # Products in actual nilpotent exponential boxes

The published finite BCH identity is transported to a chosen Lie-algebra
model. The uniform normalized structure constants then give the polynomial
product bound in the manuscript's box calculus, for every height scale and
letter support. No coordinate growth conclusion is assumed as an input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule
open scoped BigOperators Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The exponential image of the coordinate cube of radius `R`. With the
supremum norm on the coordinate functions this is exactly the usual box. -/
def exponentialCoordinateBox {G J : Type*} [Fintype J]
    (exp : L → G) (b : Basis J ℝ L) (R : ℝ) : Set G :=
  {g | ∃ x : L, exp x = g ∧ ‖b.equivFun x‖ ≤ R}

theorem mem_exponentialCoordinateBox_iff {G J : Type*} [Fintype J]
    (exp : L → G) (b : Basis J ℝ L) (R : ℝ) (hR : 0 ≤ R) (g : G) :
    g ∈ exponentialCoordinateBox exp b R ↔ ∃ x, exp x = g ∧
      ∀ j, |b.repr x j| ≤ R := by
  simp only [exponentialCoordinateBox, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hb⟩
    exact ⟨x, hx, fun j => (Real.norm_eq_abs _ ▸ norm_le_pi_norm (b.equivFun x) j).trans hb⟩
  · rintro ⟨x, hx, hb⟩
    refine ⟨x, hx, ?_⟩
    apply (pi_norm_le_iff_of_nonneg hR).mpr
    intro j
    rw [Real.norm_eq_abs]
    exact hb j

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- Transport only the finite expansion needed by the model. -/
theorem model_finiteDynkinExpansion
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥) (n : ℕ) :
    ∃ coeff : DynkinCoefficients c n, (∀ d w, |coeff d w| ≤ (2 : ℝ) ^ c) ∧
      ∀ X : Fin n → L, (List.ofFn (fun i => Exp (e (X i)))).prod =
        Exp (e (finiteDynkinPolynomial coeff X)) := by
  have hc' : lowerCentralSeries ℝ (GroupLieAlgebra (𝓘(ℝ, E)) G)
      (GroupLieAlgebra (𝓘(ℝ, E)) G) c = ⊥ := by
    rw [← LieIdeal.lowerCentralSeries_map_eq c e.surjective, hc]
    simp only [LieIdeal.map_eq_bot_iff, bot_le]
  obtain ⟨coeff, hcoeff, hprod⟩ := dynkin Exp hExp c hc' n
  refine ⟨coeff, hcoeff, fun X => ?_⟩
  exact (hprod (fun i => e (X i))).trans
    (congrArg Exp (finiteDynkinPolynomial_map e.toLieHom coeff X).symm)

/-- The polynomial product estimate in any basis with bounded brackets. -/
theorem product_mem_exponentialCoordinateBox
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {c n : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    {J : Type*} [Fintype J] (b : Basis J ℝ L)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbracket : ∀ i j l, |b.repr ⁅b i, b j⁆ l| ≤ C)
    (g : Fin n → G) (hg : ∀ i, g i ∈ exponentialCoordinateBox (Exp ∘ e) b R) :
    (List.ofFn g).prod ∈ exponentialCoordinateBox (Exp ∘ e) b
      ((c : ℝ) * 2 ^ c * (1 + (Fintype.card J : ℝ) ^ 2 * C) ^ c *
        (1 + R) ^ c * (1 + (n : ℝ)) ^ c) := by
  choose X hX hbound using hg
  obtain ⟨coeff, hcoeff, hprod⟩ := model_finiteDynkinExpansion dynkin e Exp hExp hc n
  refine ⟨finiteDynkinPolynomial coeff X, ?_,
    norm_finiteDynkinPolynomial_le b coeff hcoeff X hC hR hbracket hbound⟩
  exact (hprod X).symm.trans (congrArg List.prod (congrArg List.ofFn (funext hX)))

omit [T2Space G] in
/-- Inversion preserves every exponential coordinate box exactly. -/
theorem inv_mem_exponentialCoordinateBox
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    {J : Type*} [Fintype J] (b : Basis J ℝ L) {R : ℝ} {g : G}
    (hg : g ∈ exponentialCoordinateBox (Exp ∘ e) b R) :
    g⁻¹ ∈ exponentialCoordinateBox (Exp ∘ e) b R := by
  obtain ⟨x, rfl, hx⟩ := hg
  refine ⟨-x, ?_, ?_⟩
  · simp only [Function.comp_apply, map_neg, hExp.map_neg]
  · simpa only [map_neg, norm_neg] using hx

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Uniform polynomial multiplication in all maximizing scaled word boxes.
The constant depends only on the fixed finite Lie model. -/
theorem exists_uniform_word_box_product_bound
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : I → ℝ)
      (β : WordBasisSelections X (boundedBracketWords c)),
      IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
        (fun w => bracketWordExponent s w) β.val →
      ∀ r : ℝ, 0 ≤ r → ∀ n : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ g : Fin n → G,
      let b := exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun i => bracketWordExponent s (β.val i)) r
      (∀ i, g i ∈ exponentialCoordinateBox (Exp ∘ e) b R) →
      (List.ofFn g).prod ∈ exponentialCoordinateBox (Exp ∘ e) b
        (C * (1 + (n : ℝ)) ^ c * (1 + R) ^ c) := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_rescaled_structureConstant_bound X hc b₀
  refine ⟨(c : ℝ) * 2 ^ c * (1 + (finrank ℝ L : ℝ) ^ 2 * K) ^ c,
    by positivity, ?_⟩
  intro s β hβ r hr n R hR g
  dsimp only
  intro hg
  have hp := product_mem_exponentialCoordinateBox dynkin e Exp hExp hc
    (exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
      (fun i => bracketWordExponent s (β.val i)) r)
    hK hR (hbound s β hβ r hr) g hg
  simpa only [Fintype.card_fin, mul_assoc, mul_left_comm, mul_comm] using hp

end PolycyclicRecognition

end

end OAI
