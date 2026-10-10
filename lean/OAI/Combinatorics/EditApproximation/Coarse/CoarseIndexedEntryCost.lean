import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseIndexedWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseSeedLaw
import OAI.Combinatorics.EditApproximation.Probability.FreshCoordinateCost
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- Keep the branch dimensions symbolic when forming the finite source sum. -/


theorem coarseIndexedEntryBinaryCost_computed_bound :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (_hB : NeZero B) (draw : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseIndexedEntryBinaryCost N B d x y draw : ℝ) ≤ (inputHeight N : ℝ) ^ 40 *
        ((coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draw : ℝ) +
          (x.length + 1 : ℕ)) := by
  filter_upwards [BinaryFraction.computedCoarseIndexedInitialWithWork_bound] with N hN
  intro B d x y hB hd hxy hsymbols hinstance draw
  have hb := hN B d x y hB hd hxy hsymbols
    (Nat.pos_of_neZero _) (pow_pos (Nat.two_pow_pos _) _)
    (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) draw
  exact_mod_cast hb



theorem coarseIndexedEntryCostSum_bound {M J B : ℕ} [NeZero B] (source target : List ℕ)
    (N : ℕ) (depth : PhysicalEntry M J target.length → ℕ)
    (draw : PhysicalCoarseDraw source target B depth)
    (selected : PhysicalEntry M J target.length → Prop) (C : ℝ)
    (hc : ∀ entry : PhysicalEntry M J target.length,
      (coarseIndexedEntryBinaryCost N B (depth entry) (physicalSource source entry.1)
        (substring target entry.2.lo entry.2.hi) (draw entry) : ℝ) ≤
        C * ((coarseInitialArrayWork B (depth entry) (initialThresholdQ N) (initialLambda N)
          (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (draw entry) : ℝ) +
          ((physicalSource source entry.1).length + 1 : ℕ))) :
    coarseIndexedEntryCostSum source target N depth draw selected ≤ C *
      ((∑ entry : PhysicalEntry M J target.length, selectionIndicator (selected entry) *
        (coarseInitialArrayWork B (depth entry) (initialThresholdQ N) (initialLambda N)
          (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (draw entry) : ℝ)) +
        ∑ entry : PhysicalEntry M J target.length, selectionIndicator (selected entry) *
          ((physicalSource source entry.1).length + 1 : ℕ)) := by
  classical
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  unfold coarseIndexedEntryCostSum
  apply Finset.sum_le_sum
  intro entry _
  have hs : 0 ≤ selectionIndicator (selected entry) := by
    unfold selectionIndicator
    split <;> norm_num
  exact (mul_le_mul_of_nonneg_left (hc entry) hs).trans_eq (by ring)

end EditApproximation

end OAI
