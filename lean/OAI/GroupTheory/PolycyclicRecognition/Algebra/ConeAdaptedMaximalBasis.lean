import OAI.GroupTheory.PolycyclicRecognition.Algebra.ConeIdealBasisExchange
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BasisQuotientLifts

namespace OAI

/-! # The ideal and ambient boxes have the same maximal width exponent -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set
open scoped BigOperators

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

/-- Completing a maximal mixed-word ideal basis by pure quotient words
gives a maximal ambient word basis, with exactly the same total width. -/
theorem exists_cone_adapted_maximal_basis_data
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → s i = 0)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C bI s β) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (q : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        FreeMagma (Fin M.letterCount)),
      (∀ j, ¬IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (q j)) ∧
      ∃ hq : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (evalBracketWord M.letter (q j)) = bQ j,
      ∃ (e : (Fin (finrank ℝ (M.coneWordIdeal C)) ⊕
        Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))) ≃
          Fin (finrank ℝ (cartanRootIdeal H))) (γ : M.Bases),
      WordBasisSelections.basis M.letter M.wordList γ =
        (basisWithQuotientLifts (M.coneWordIdeal C).toSubmodule
          (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β)
          bQ (fun j => evalBracketWord M.letter (q j)) hq).reindex e ∧
      (∀ k, bracketWordExponent s (γ.val k) =
        Sum.elim (fun j => M.coneIdealWordCost C s (β.val j)) (fun _ => 0) (e.symm k)) ∧
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
        (fun w => bracketWordExponent s w) γ.val ∧
      columnBasisWeight (fun w : M.wordList => bracketWordExponent s w) γ.val =
        columnBasisWeight (fun w : M.coneIdealWordList C => M.coneIdealWordCost C s w) β.val := by
  classical
  let U := (M.coneWordIdeal C).toSubmodule
  let b := WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β
  have hquot : ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ U)))
      ℝ (cartanRootIdeal H ⧸ U))
      (q : Fin (finrank ℝ (cartanRootIdeal H ⧸ U)) → FreeMagma (Fin M.letterCount)),
      (∀ j, ¬IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) (q j)) ∧
      (∀ j, U.mkQ (evalBracketWord M.letter (q j)) = bQ j) :=
    exists_pure_quotient_word_basis M.letter
      (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) M.generates
  obtain ⟨bQ, q, hpure, hq⟩ := hquot
  let W := Fin (finrank ℝ (M.coneWordIdeal C)) ⊕ Fin (finrank ℝ (cartanRootIdeal H ⧸ U))
  let B : Basis W ℝ (cartanRootIdeal H) :=
    basisWithQuotientLifts U b bQ (fun j => evalBracketWord M.letter (q j)) hq
  let words : W → FreeMagma (Fin M.letterCount) :=
    Sum.elim (fun j => M.coneOriginalWord C (β.val j)) q
  have heval (k : W) : evalBracketWord M.letter (words k) = B k := by
    cases k with
    | inl j =>
      change evalBracketWord M.letter (M.coneOriginalWord C (β.val j)) = _
      rw [M.coneOriginalWord_eval]
      rw [show B (Sum.inl j) = (b j : cartanRootIdeal H) from
        basisWithQuotientLifts_inl U b bQ _ hq j]
      exact congrArg Subtype.val
        (WordBasisSelections.eval_words (M.coneMixedVector C) (M.coneIdealWordList C) β j)
    | inr j => exact (basisWithQuotientLifts_inr U b bQ _ hq j).symm
  have hmem (k : W) : words k ∈ M.wordList :=
    M.mem_wordList_of_eval_ne_zero _ (fun hz => B.ne_zero k ((heval k).symm.trans hz))
  let e : W ≃ Fin (finrank ℝ (cartanRootIdeal H)) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis B).symm
  let γ : M.Bases := ⟨fun k => ⟨words (e.symm k), hmem (e.symm k)⟩,
    B.reindex e, fun k => (heval (e.symm k)).trans (B.reindex_apply e k).symm⟩
  have hγ : WordBasisSelections.basis M.letter M.wordList γ = B.reindex e := by
    apply Basis.eq_of_apply_eq
    intro k
    exact (WordBasisSelections.eval_words M.letter M.wordList γ k).symm.trans
      ((heval (e.symm k)).trans (B.reindex_apply e k).symm)
  have hqzero (j) : bracketWordExponent s (q j) = 0 :=
    bracketWordExponent_eq_zero_of_pure s _ (fun i hi => hzero i (not_not.mp hi)) _ (hpure j)
  have hsupport (w : M.wordList) (k : Fin (finrank ℝ (cartanRootIdeal H)))
      (hk : (WordBasisSelections.basis M.letter M.wordList γ).repr
        (evalBracketWord M.letter w) k ≠ 0) :
      bracketWordExponent s w ≤ bracketWordExponent s (γ.val k) := by
    rw [hγ, Basis.repr_reindex_apply] at hk
    by_cases hw : IsMixedWord (fun i => (M.weight i : H →ₗ[ℝ] ℝ) ∉ C) w
    · let wm : M.coneMixedWords C := ⟨w, hw⟩
      cases he : e.symm k with
      | inl i =>
        rw [he] at hk
        change B.repr (M.coneMixedVector C wm : cartanRootIdeal H) (Sum.inl i) ≠ 0 at hk
        have hki : b.repr (M.coneMixedVector C wm) i ≠ 0 := by
          simpa only [B, ← basisWithQuotientLifts_repr_inl U b bQ _ hq
            (M.coneMixedVector C wm) i] using hk
        have hle := M.coneIdeal_width_le_of_coordinate_ne_zero C bI s β hβ wm i hki
        change bracketWordExponent s w ≤ bracketWordExponent s (words (e.symm k))
        rw [he]
        exact hle.trans_eq (M.coneIdealWordCost_eq_original C s (β.val i))
      | inr i =>
        rw [he] at hk
        have hz : U.mkQ (evalBracketWord M.letter w) = 0 :=
          (Submodule.Quotient.mk_eq_zero U).mpr (eval_mixed_mem_span M.letter _ hw)
        have hc := basisWithQuotientLifts_repr_inr U b bQ _ hq (evalBracketWord M.letter w) i
        change B.repr (evalBracketWord M.letter w) (Sum.inr i) = _ at hc
        rw [hc, hz, map_zero, Finsupp.zero_apply] at hk
        exact (hk rfl).elim
    · rw [bracketWordExponent_eq_zero_of_pure s _
        (fun i hi => hzero i (not_not.mp hi)) w hw]
      exact bracketWordExponent_nonneg s hs (γ.val k)
  have hcost (k) : bracketWordExponent s (γ.val k) =
      Sum.elim (fun j => M.coneIdealWordCost C s (β.val j)) (fun _ => 0) (e.symm k) := by
    change bracketWordExponent s (words (e.symm k)) = _
    cases he : e.symm k with
    | inl j => exact (M.coneIdealWordCost_eq_original C s (β.val j)).symm
    | inr j => exact hqzero j
  refine ⟨bQ, q, hpure, hq, e, γ, hγ, hcost, ?_, ?_⟩
  · apply maximizingColumnBasis_of_coordinate_support _ _ _
      (wordBasis_det_ne_zero M.letter M.wordList bN γ)
    intro w k hk
    rw [columnCoordinates_eq_wordBasis_repr M.letter M.wordList bN γ w] at hk
    exact hsupport w k hk
  · change (∑ k, bracketWordExponent s (words (e.symm k))) = _
    calc
      _ = ∑ w : W, bracketWordExponent s (words w) :=
        Equiv.sum_comp e.symm (fun w => bracketWordExponent s (words w))
      _ = _ := by
        rw [Fintype.sum_sum_type]
        simp only [words, Sum.elim_inl, Sum.elim_inr, hqzero, Finset.sum_const_zero,
          add_zero, ← M.coneIdealWordCost_eq_original]
        rfl

/-- The adapted ambient basis has exactly the maximal ideal width sum. -/
theorem exists_cone_adapted_maximal_basis
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hzero : ∀ i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C → s i = 0)
    (β : M.ConeIdealBases C) (hβ : M.IsMaximizingConeIdealBasis C bI s β) :
    ∃ γ : M.Bases,
      IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
        (fun w => bracketWordExponent s w) γ.val ∧
      columnBasisWeight (fun w : M.wordList => bracketWordExponent s w) γ.val =
        columnBasisWeight (fun w : M.coneIdealWordList C => M.coneIdealWordCost C s w) β.val := by
  obtain ⟨_, _, _, _, _, γ, _, _, hmax, hsum⟩ :=
    M.exists_cone_adapted_maximal_basis_data C bN bI s hs hzero β hβ
  exact ⟨γ, hmax, hsum⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
