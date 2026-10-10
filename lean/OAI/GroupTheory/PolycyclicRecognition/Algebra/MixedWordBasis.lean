import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealGroup

namespace OAI

/-! # Finite mixed-word spanning pools for the cone ideals -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)

def coneMixedWords (C : Set (H →ₗ[ℝ] ℝ)) :=
  {w : M.wordList // IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) w}

instance (C : Set (H →ₗ[ℝ] ℝ)) : Fintype (M.coneMixedWords C) := by
  classical
  unfold coneMixedWords
  infer_instance

instance (C : Set (H →ₗ[ℝ] ℝ)) : DecidableEq (M.coneMixedWords C) :=
  Classical.decEq _

def coneMixedVector (C : Set (H →ₗ[ℝ] ℝ)) (w : M.coneMixedWords C) : M.coneWordIdeal C :=
  ⟨evalBracketWord M.letter w.val, eval_mixed_mem_span M.letter _ w.property⟩

theorem coneWordIdeal_eq_span_finite_mixed (C : Set (H →ₗ[ℝ] ℝ)) :
    (M.coneWordIdeal C).toSubmodule =
      Submodule.span ℝ (range (fun w : M.coneMixedWords C => evalBracketWord M.letter w.val)) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    by_cases hz : evalBracketWord M.letter w = 0
    · rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span
        ⟨⟨⟨w, M.mem_wordList_of_eval_ne_zero w hz⟩, hw⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact eval_mixed_mem_span M.letter _ w.property

theorem coneMixedVector_span (C : Set (H →ₗ[ℝ] ℝ)) :
    Submodule.span ℝ (range (M.coneMixedVector C)) = ⊤ := by
  let I := (M.coneWordIdeal C).toSubmodule
  apply Submodule.map_injective_of_injective I.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, I.range_subtype]
  change _ = (M.coneWordIdeal C).toSubmodule
  conv_rhs => rw [M.coneWordIdeal_eq_span_finite_mixed C]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨M.coneMixedVector C w, ⟨w, rfl⟩, rfl⟩

theorem exists_cone_mixed_word_basis (C : Set (H →ₗ[ℝ] ℝ)) :
    ∃ (b : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
      (words : Fin (finrank ℝ (M.coneWordIdeal C)) → M.coneMixedWords C),
      ∀ j, M.coneMixedVector C (words j) = b j := by
  let S := range (M.coneMixedVector C)
  have hS : ⊤ ≤ Submodule.span ℝ S := (M.coneMixedVector_span C).ge
  let J := (linearIndepOn_empty ℝ (id : M.coneWordIdeal C → M.coneWordIdeal C)).extend
    (empty_subset S)
  let b₀ : Basis J ℝ (M.coneWordIdeal C) := Basis.ofSpan hS
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin (finrank ℝ (M.coneWordIdeal C)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  let b := b₀.reindex e
  have hw (j) : ∃ w, M.coneMixedVector C w = b j := by
    have hj := Basis.ofSpan_subset hS (show b₀ (e.symm j) ∈ range b₀ from ⟨_, rfl⟩)
    simpa only [b, Basis.coe_reindex, Function.comp_apply, S, Set.mem_range] using hj
  choose words hwords using hw
  exact ⟨b, words, hwords⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
