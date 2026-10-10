import OAI.GroupTheory.PolycyclicRecognition.Algebra.MixedWordIdeal
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HomogeneousGenerators

namespace OAI

/-! # Pure word bases of the mixed-word quotient

An inside generator is retained in every pure word basis. The proof uses
its actual coordinate in the original abelianization, descended through
the mixed-word ideal.
-/

noncomputable section
namespace PolycyclicRecognition

open Module Set
open scoped BigOperators

variable {I L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem exists_pure_quotient_word_basis [FiniteDimensional ℝ L]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤) :
    let J := (mixedWordIdeal X outside hgen).toSubmodule
    ∃ (b : Basis (Fin (finrank ℝ (L ⧸ J))) ℝ (L ⧸ J))
      (words : Fin (finrank ℝ (L ⧸ J)) → FreeMagma I),
      (∀ j, ¬IsMixedWord outside (words j)) ∧
      (∀ j, J.mkQ (evalBracketWord X (words j)) = b j) := by
  dsimp only
  let J := (mixedWordIdeal X outside hgen).toSubmodule
  let S := J.mkQ '' (evalBracketWord X '' {w | ¬IsMixedWord outside w})
  have hS : ⊤ ≤ Submodule.span ℝ S :=
    (quotient_mixedWordIdeal_span_pure X outside hgen).ge
  let K := (linearIndepOn_empty ℝ (id : (L ⧸ J) → (L ⧸ J))).extend
    (empty_subset S)
  let b₀ : Basis K ℝ (L ⧸ J) := Basis.ofSpan hS
  let : Fintype K := Fintype.ofFinite _
  let e : K ≃ Fin (finrank ℝ (L ⧸ J)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hw (j) : ∃ w, ¬IsMixedWord outside w ∧ J.mkQ (evalBracketWord X w) = b j := by
    have hj := Basis.ofSpan_subset hS (show b₀ (e.symm j) ∈ range b₀ from ⟨_, rfl⟩)
    obtain ⟨_, ⟨w, hp, rfl⟩, he⟩ := hj
    exact ⟨w, hp, by simpa only [b, Basis.coe_reindex, Function.comp_apply] using he⟩
  choose words hp he using hw
  exact ⟨b, words, hp, he⟩

variable [DecidableEq I]

omit [DecidableEq I] in
/-- An inside abelian coordinate vanishes on the entire mixed-word ideal. -/
theorem inside_abelian_coordinate_kills_mixed
    {Q : Type*} [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (i : I) (hi : ¬outside i) :
    mixedWordSpan X outside ≤ LinearMap.ker ((bq.coord i).comp q) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, hw, rfl⟩
  change bq.repr (q (evalBracketWord X w)) i = 0
  cases w with
  | of j =>
    have hij : i ≠ j := fun he => hi (he ▸ hw)
    simp [evalBracketWord, hX, hij]
  | mul u v => simp [evalBracketWord, hq]

omit [DecidableEq I] in
/-- Every retained generator occurs as a one-letter word in any pure
word basis of the quotient. -/
theorem mandatory_inside_letter_in_quotient
    {Q K : Type*} [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis K ℝ (L ⧸ (mixedWordIdeal X outside hgen).toSubmodule))
    (words : K → FreeMagma I)
    (hwords : ∀ j, (mixedWordIdeal X outside hgen).toSubmodule.mkQ
      (evalBracketWord X (words j)) = b j)
    (i : I) (hi : ¬outside i) : ∃ j, words j = .of i := by
  let J := (mixedWordIdeal X outside hgen).toSubmodule
  let f := (bq.coord i).comp q
  let fQ := J.liftQ f (inside_abelian_coordinate_kills_mixed X outside q hq bq hX i hi)
  by_contra hn
  have hn' : ∀ j, words j ≠ .of i := fun j h => hn ⟨j, h⟩
  have hf : fQ = 0 := b.ext fun j => by
    rw [← hwords j]
    change f (evalBracketWord X (words j)) = 0
    cases hw : words j with
    | of k =>
      have hki : k ≠ i := fun h => hn' j (hw.trans (congrArg FreeMagma.of h))
      simp [f, evalBracketWord, hX, Basis.coord_apply, hki]
    | mul u v => simp [f, evalBracketWord, hq]
  have h := congrArg (fun F : (L ⧸ J) →ₗ[ℝ] ℝ => F (J.mkQ (X i))) hf
  change f (X i) = 0 at h
  simp [f, hX, Basis.coord_apply] at h

theorem positive_inside_quotient_word_counts
    [Fintype I] {Q K : Type*} [Fintype K] [AddCommGroup Q] [Module ℝ Q]
    (X : I → L) (outside : I → Prop)
    (hgen : LieSubalgebra.lieSpan ℝ L (range X) = ⊤)
    (q : L →ₗ[ℝ] Q) (hq : ∀ x y : L, q ⁅x, y⁆ = 0)
    (bq : Basis I ℝ Q) (hX : ∀ i, q (X i) = bq i)
    (b : Basis K ℝ (L ⧸ (mixedWordIdeal X outside hgen).toSubmodule))
    (words : K → FreeMagma I)
    (hwords : ∀ j, (mixedWordIdeal X outside hgen).toSubmodule.mkQ
      (evalBracketWord X (words j)) = b j)
    (i : I) (hi : ¬outside i) : 0 < ∑ j, bracketWordCount (words j) i := by
  obtain ⟨j, hj⟩ := mandatory_inside_letter_in_quotient X outside hgen q hq bq hX
    b words hwords i hi
  have hle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset K)) =>
    Nat.zero_le (bracketWordCount (words j) i)) (Finset.mem_univ j)
  rw [hj] at hle
  simp only [bracketWordCount, ite_true] at hle
  exact lt_of_lt_of_le Nat.zero_lt_one hle

end PolycyclicRecognition

end

end OAI
