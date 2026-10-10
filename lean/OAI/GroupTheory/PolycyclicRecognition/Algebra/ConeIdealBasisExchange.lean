import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConeIdealBoxCalculus
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MaximizingCoordinateCriterion

namespace OAI

/-! # Original-word coordinate exchange inside the cone ideal -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule

theorem bracketWordExponent_eq_zero_of_pure {I : Type*} [Fintype I] [DecidableEq I]
    (s : I → ℝ) (outside : I → Prop) (hs : ∀ i, ¬outside i → s i = 0)
    (w : FreeMagma I) (hw : ¬IsMixedWord outside w) : bracketWordExponent s w = 0 := by
  induction w using FreeMagma.rec with
  | of i => exact (bracketWordExponent_of s i).trans (hs i hw)
  | mul u v hu hv =>
    change bracketWordExponent s (u * v) = 0
    rw [bracketWordExponent_mul, hu (fun h => hw (Or.inl h)),
      hv (fun h => hw (Or.inr h)), add_zero]

namespace CartanWordModel

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ))

theorem coneIdeal_leaf_mem_of_ne_zero (w : M.coneMixedWords C)
    (hw : M.coneMixedVector C w ≠ 0) : FreeMagma.of w ∈ M.coneIdealWordList C := by
  apply (mem_boundedBracketWords _ _).mpr
  change 0 < M.coneIdealWordBound C
  by_contra hn
  have hh := evalBracketWord_eq_zero_of_depth (M.coneMixedVector C)
    (M.coneIdealWordBound_zero C) (FreeMagma.of w)
    (by simpa only [bracketWordDepth] using Nat.le_of_not_gt hn)
  exact hw hh

/-- Exchange applies to every original mixed word, even though the ideal
box is built using the nested finite alphabet. -/
theorem coneIdeal_width_le_of_coordinate_ne_zero
    (b₀ : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (s : Fin M.letterCount → ℝ) (β : M.ConeIdealBases C)
    (hβ : M.IsMaximizingConeIdealBasis C b₀ s β) (w : M.coneMixedWords C)
    (j : Fin (finrank ℝ (M.coneWordIdeal C)))
    (hj : (WordBasisSelections.basis (M.coneMixedVector C) (M.coneIdealWordList C) β).repr
      (M.coneMixedVector C w) j ≠ 0) :
    bracketWordExponent s w.val.val ≤ M.coneIdealWordCost C s (β.val j) := by
  have hw : M.coneMixedVector C w ≠ 0 := by
    intro hz
    apply hj
    rw [hz, map_zero, Finsupp.zero_apply]
  let z : M.coneIdealWordList C := ⟨FreeMagma.of w, M.coneIdeal_leaf_mem_of_ne_zero C w hw⟩
  let v := wordListCoordinates (M.coneMixedVector C) (M.coneIdealWordList C) b₀
  have hc : columnCoordinates v β.val z j ≠ 0 := by
    rw [columnCoordinates_eq_wordBasis_repr]
    exact hj
  have hh := weight_le_of_nonzero_coordinate v
    (fun z : M.coneIdealWordList C => M.coneIdealWordCost C s z) β.val hβ z j
    (columnCoordinates v β.val z) (columnCoordinates_repr v β.val hβ.1 z) hc
  simpa only [z, coneIdealWordCost, bracketWordExponent_of] using hh

end CartanWordModel
end PolycyclicRecognition

end

end OAI
