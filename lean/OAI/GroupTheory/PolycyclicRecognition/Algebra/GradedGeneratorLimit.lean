import OAI.GroupTheory.PolycyclicRecognition.Algebra.GradedCoordinateLimit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedGroupLaws

namespace OAI

/-! # Generating vectors and group laws survive the graded limit -/

noncomputable section

namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Topology

variable {L I : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype I] [DecidableEq I]

/-- The part of a vector whose coordinate degree equals the prescribed
generator degree. -/
def gradedGenerator {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (s : ℝ) (x : L) : Fin n → ℝ :=
  fun j => if s = cost j then b.repr x j else 0

theorem rescaled_generator_tendsto
    {n : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ) (s : ℝ) (x : L)
    (hweight : ∀ j, b.repr x j ≠ 0 → s ≤ cost j) :
    Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).equivFun
      (Real.exp (r * s) • x)) atTop (𝓝 (gradedGenerator b cost s x)) := by
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun r : ℝ => (exponentialRescaleBasis b cost r).repr
    (Real.exp (r * s) • x) j) atTop (𝓝 (if s = cost j then b.repr x j else 0))
  simp_rw [repr_exponentialRescaleBasis_smul]
  by_cases hz : b.repr x j = 0
  · simp only [hz, zero_mul, ite_self]
    exact tendsto_const_nhds
  by_cases he : s = cost j
  · simp only [he, sub_self, mul_zero, Real.exp_zero, mul_one]
    exact tendsto_const_nhds
  · have hlt : s - cost j < 0 := sub_neg.mpr (lt_of_le_of_ne (hweight j hz) he)
    have ht := Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_neg hlt).mpr tendsto_id)
    simpa [he, Function.comp_def] using ht.const_mul (b.repr x j)

/-- Basis maximality prevents a generator from having a nonzero coordinate
of lower degree. -/
theorem maximizing_word_basis_letter_weight
    (X : I → L) (S : Finset (FreeMagma I)) (hletters : ∀ i, FreeMagma.of i ∈ S)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
    (β : WordBasisSelections X S)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X S b₀)
      (fun w => bracketWordExponent s w) β.val)
    (i : I) (j : Fin (finrank ℝ L))
    (hnz : (WordBasisSelections.basis X S β).repr (X i) j ≠ 0) :
    s i ≤ bracketWordExponent s (β.val j) := by
  let w : S := ⟨.of i, hletters i⟩
  have hc : columnCoordinates (wordListCoordinates X S b₀) β.val w j =
      (WordBasisSelections.basis X S β).repr (X i) j := by
    rw [columnCoordinates_eq_wordBasis_repr]
    rfl
  have hw := weight_le_of_nonzero_coordinate (wordListCoordinates X S b₀)
    (fun w => bracketWordExponent s w) β.val hβ w j
    (columnCoordinates (wordListCoordinates X S b₀) β.val w)
    (columnCoordinates_repr _ _ hβ.1 w) (by rw [hc]; exact hnz)
  simpa only [w, bracketWordExponent_of] using hw

/-- The actual rescaled bracket and all actual generators converge together. -/
theorem rescaledLieData_tendsto_graded
    (X : I → L) {k : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent s (β.val j)
    Tendsto (rescaledLieData X (boundedBracketWords k) β s) atTop
      (𝓝 (gradedCoordinateBracket b cost, fun i => gradedGenerator b cost (s i) (X i))) := by
  dsimp only
  apply Tendsto.prodMk_nhds
  · exact basisBracket_rescale_tendsto _ _ (maximizing_word_basis_bracket_weight X hk b₀ s β hβ)
  · apply tendsto_pi_nhds.mpr
    intro i
    exact rescaled_generator_tendsto _ _ _ _
      (maximizing_word_basis_letter_weight X _ hletters b₀ s β hβ i)

/-- Every selected bracket word still evaluates to its coordinate unit in
the graded limit. Thus the limiting generators span the whole Lie algebra
under brackets; the limit has not lost any directions. -/
theorem graded_generators_word_normalization
    (X : I → L) {k : ℕ} (hk : lowerCentralSeries ℝ L L k = ⊥)
    (hletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords k)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L) (s : I → ℝ)
    (β : WordBasisSelections X (boundedBracketWords k))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords k) b₀)
      (fun w => bracketWordExponent s w) β.val) :
    let b := WordBasisSelections.basis X (boundedBracketWords k) β
    let cost := fun j => bracketWordExponent s (β.val j)
    ∀ j, evalBilinearWord (gradedCoordinateBracket b cost)
      (fun i => gradedGenerator b cost (s i) (X i)) (β.val j) = Pi.single j 1 := by
  exact (isClosed_wordNormalizations (fun j => (β.val j : FreeMagma I))
    (fun j => (Pi.single j (1 : ℝ) : Fin (finrank ℝ L) → ℝ))).mem_of_tendsto
      (rescaledLieData_tendsto_graded X hk hletters b₀ s β hβ)
      (Eventually.of_forall (fun r => rescaledLieData_word X _ β s r))

/-- The fixed finite Dynkin product retains its exact group and straight-line
one-parameter identities in the limiting coordinate law. -/
theorem gradedCoordinateBracket_groupLaws
    {G : Type*} [Group G] {n c : ℕ} (b : Basis (Fin n) ℝ L) (cost : Fin n → ℝ)
    (hweight : ∀ i j k, b.repr ⁅b i, b j⁆ k ≠ 0 → cost i + cost j ≤ cost k)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hzero : Exp 0 = 1) (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y) :
    PolynomialGroupLaws (dynkinProduct a (gradedCoordinateBracket b cost)) :=
  (isClosed_dynkinGroupLaws a).mem_of_tendsto (basisBracket_rescale_tendsto b cost hweight)
    (Eventually.of_forall (fun r =>
      basis_polynomialGroupLaws (exponentialRescaleBasis b cost r) Exp hinj hzero hneg hadd a hm))

end PolycyclicRecognition

end

end OAI
