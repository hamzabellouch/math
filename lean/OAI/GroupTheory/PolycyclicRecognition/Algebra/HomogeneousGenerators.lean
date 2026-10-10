import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentGenerators
import Mathlib.LinearAlgebra.Quotient.Basic

namespace OAI

/-! # Choosing generators and their positive word multiplicities

A basis of the abelianization can be selected from any homogeneous spanning
pool. Its lifts generate the nilpotent algebra. Every bracket-word basis
then uses every selected generator, which is the positivity needed in the
support-volume formula.
-/

noncomputable section

namespace PolycyclicRecognition

open Module
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem exists_quotient_basis_lifts [FiniteDimensional ℝ L]
    (N : Submodule ℝ L) (S : Set L) (hS : Submodule.span ℝ S ⊔ N = ⊤) :
    ∃ (b : Basis (Fin (Module.finrank ℝ (L ⧸ N))) ℝ (L ⧸ N))
      (X : Fin (Module.finrank ℝ (L ⧸ N)) → L),
      (∀ i, X i ∈ S) ∧ (∀ i, N.mkQ (X i) = b i) ∧
      Submodule.span ℝ (Set.range X) ⊔ N = ⊤ := by
  have himage : Submodule.span ℝ (N.mkQ '' S) = ⊤ := by
    rw [← Submodule.map_span, N.map_mkQ_eq_top]
    simpa only [sup_comm] using hS
  let J := (linearIndepOn_empty ℝ (id : (L ⧸ N) → (L ⧸ N))).extend
    (Set.empty_subset (N.mkQ '' S))
  let b₀ : Basis J ℝ (L ⧸ N) := Basis.ofSpan himage.ge
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin (Module.finrank ℝ (L ⧸ N)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hlift : ∀ i, ∃ x ∈ S, N.mkQ x = b i := by
    intro i
    simpa only [b, Basis.coe_reindex, Function.comp_apply, Set.mem_image] using
      (Basis.ofSpan_subset himage.ge
        (show b₀ (e.symm i) ∈ Set.range b₀ from ⟨_, rfl⟩))
  choose X hXS hX using hlift
  refine ⟨b, X, hXS, hX, ?_⟩
  rw [sup_comm, ← N.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have heq : N.mkQ ∘ X = b := funext hX
  rw [heq]
  exact b.span_eq

variable {I : Type*} [DecidableEq I]

/-- An abelian coordinate of a word without the corresponding letter is zero. -/
theorem abelian_coordinate_eval_eq_zero_of_count_zero
    (X : I → L) (f : L →ₗ[ℝ] ℝ) (i : I)
    (hbracket : ∀ x y : L, f ⁅x, y⁆ = 0)
    (hX : ∀ j, j ≠ i → f (X j) = 0)
    (w : FreeMagma I) (hw : bracketWordCount w i = 0) :
    f (evalBracketWord X w) = 0 := by
  cases w with
  | of j =>
    have hij : i ≠ j := by
      intro heq
      simp [bracketWordCount, heq] at hw
    exact hX j hij.symm
  | mul a b => exact hbracket _ _

/-- Every abelianization-basis letter occurs as an actual one-letter word
in every word basis, since all longer words vanish in the abelian quotient. -/
theorem mandatory_letter_of_abelianization
    {J Q : Type*} [Fintype J] [AddCommGroup Q] [Module ℝ Q]
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (X : I → L) (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis J ℝ L) (words : J → FreeMagma I)
    (hwords : ∀ j, evalBracketWord X (words j) = b j) (i : I) :
    ∃ j, words j = .of i := by
  by_contra hn
  have hn' : ∀ j, words j ≠ .of i := fun j h => hn ⟨j, h⟩
  let f := (bq.coord i).comp q
  have hf : f = 0 := b.ext fun j => by
    rw [← hwords]
    cases hw : words j with
    | of k =>
      have hki : k ≠ i := by
        intro heq
        exact hn' j (hw.trans (congrArg FreeMagma.of heq))
      simp [f, evalBracketWord, hX, Basis.coord_apply, hki]
    | mul u v => simp [f, evalBracketWord, hq]
  have hi := congrArg (fun F : L →ₗ[ℝ] ℝ => F (X i)) hf
  simp [f, hX, Basis.coord_apply] at hi

/-- Every word basis uses every generator whose images are a basis in an
abelian quotient. In particular its total letter count is strictly positive. -/
theorem positive_bracketWord_multiplicities
    [Fintype I] {J Q : Type*} [Fintype J]
    [AddCommGroup Q] [Module ℝ Q]
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (X : I → L) (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis J ℝ L) (words : J → FreeMagma I)
    (hwords : ∀ j, evalBracketWord X (words j) = b j) :
    ∀ i, 0 < ∑ j, bracketWordCount (words j) i := by
  intro i
  by_contra hn
  have hcounts : ∀ j, bracketWordCount (words j) i = 0 := by
    have hsum : ∑ j, bracketWordCount (words j) i = 0 := Nat.eq_zero_of_not_pos hn
    exact fun j => Nat.eq_zero_of_le_zero
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans hsum.le)
  let f := (bq.coord i).comp q
  have hf : f = 0 := b.ext fun j => by
    rw [← hwords]
    apply abelian_coordinate_eval_eq_zero_of_count_zero X f i
    · intro x y
      simp only [f, LinearMap.comp_apply, hq, map_zero]
    · intro k hk
      simp [f, hX, Basis.coord_apply, hk]
    · exact hcounts j
  have h := congrArg (fun F : L →ₗ[ℝ] ℝ => F (X i)) hf
  simp [f, hX, Basis.coord_apply] at h

/-- Extract the finite word data needed by the box construction from a
generating pool, retaining membership in that pool for every chosen letter. -/
theorem exists_positive_word_basis [FiniteDimensional ℝ L] [LieRing.IsNilpotent L]
    (S : Set L) (hS : LieSubalgebra.lieSpan ℝ L S = ⊤) :
    ∃ (m : ℕ) (X : Fin m → L)
      (b : Basis (Fin (Module.finrank ℝ L)) ℝ L)
      (words : Fin (Module.finrank ℝ L) → FreeMagma (Fin m)),
      (∀ i, X i ∈ S) ∧ (∀ j, evalBracketWord X (words j) = b j) ∧
      (∀ i, 0 < ∑ j, bracketWordCount (words j) i) := by
  let N := (LieModule.lowerCentralSeries ℝ L L 1).toSubmodule
  obtain ⟨bq, X, hXS, hXq, hXspan⟩ := exists_quotient_basis_lifts N S
    (span_sup_lowerCentralSeries_one_of_lieSpan S hS)
  obtain ⟨b, hb⟩ := exists_bracketWord_basis_of_abelianization X hXspan
  choose words hwords using hb
  refine ⟨Module.finrank ℝ (L ⧸ N), X, b, words, hXS, hwords, ?_⟩
  apply positive_bracketWord_multiplicities N.mkQ _ X bq hXq b words hwords
  intro x y
  apply (Submodule.Quotient.mk_eq_zero N).mpr
  change ⁅x, y⁆ ∈ LieModule.lowerCentralSeries ℝ L L (0 + 1)
  rw [LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero]
  exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)

end PolycyclicRecognition

end

end OAI
