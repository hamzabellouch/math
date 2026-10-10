import OAI.Combinatorics.EditApproximation.Refinement.ComputedEarlierInputBudget

namespace OAI

/-! A query gathers only its preceding history, rather than allocating
the full time range used to bound that history's cardinality. -/

namespace EditApproximation

theorem wideEarlierInputCover_mono_history {nx ny M : ℕ} (parent : TargetInterval nx)
    (P small large : ℕ) (representatives : List (ℕ × TargetInterval ny)) (h : small ≤ large) :
    wideEarlierInputCover (M := M) parent P small representatives ⊆
      wideEarlierInputCover parent P large representatives := by
  intro input hinput
  obtain ⟨br, hbr, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨i, hi, hinput⟩ := Finset.mem_biUnion.mp hinput
  obtain ⟨t, ht, hinput⟩ := Finset.mem_biUnion.mp hinput
  exact Finset.mem_biUnion.mpr ⟨br, hbr, Finset.mem_biUnion.mpr ⟨i, hi,
    Finset.mem_biUnion.mpr ⟨t, (Finset.mem_range.mpr ((Finset.mem_range.mp ht).trans_le h)), hinput⟩⟩⟩

theorem computed_queryEarlierHistory_card {nx ny : ℕ}
    (parent : TargetInterval nx) (N P history : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hPeq : P = (integerParameters N).P)
    (hhistory : history ≤ (integerParameters N).T + (integerParameters N).S + 1)
    (A : ℚ) (hA : A ≤ ((integerParameters N).initialFactor : ℚ))
    (initial : TargetInterval ny → ℚ) (q : TargetInterval ny) (hw : 0 ≤ initial q) :
    (queryEarlierInputCover (M := (integerParameters N).M) parent N P (inputSmallLog N)
      (40 * smallLogExponent N) history (refinementFactor A (inputSmallLog N)) initial q).card ≤
      inputHeight N ^ (256 * (coarseExponent (inputSmallLog N) + 1)) := by
  apply (Finset.card_le_card (wideEarlierInputCover_mono_history parent P history
    ((integerParameters N).T + (integerParameters N).S + 1) _ hhistory)).trans
  exact computed_queryEarlierInputCover_card parent N P hN hell hPeq A hA initial q hw

end EditApproximation

end OAI
