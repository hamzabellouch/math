import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseInitialWork
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseSeedLaw
import OAI.Combinatorics.EditApproximation.Probability.FreshCoordinateCost

namespace OAI

namespace EditApproximation

/-- Keep the branch dimensions symbolic when forming the finite source sum. -/
def coarseEntryBinaryCost (N B d : ℕ) [NeZero B] (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ :=
  (BinaryFraction.coarseInitialWithWork (inputHeight N ^ 4) (64 * inputHeight N) N
    (Nat.pos_of_neZero B) (pow_pos (Nat.two_pow_pos _) _)
    (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) x y draws).2

theorem coarseEntryBinaryCost_computed_bound :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → (∀ a ∈ x ++ y, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ (_hB : NeZero B) (draw : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      (coarseEntryBinaryCost N B d x y draw : ℝ) ≤ (inputHeight N : ℝ) ^ 36 *
        ((coarseInitialArrayWork B d (initialThresholdQ N) (initialLambda N) x y draw : ℝ) +
          (x.length + 1 : ℕ)) := by
  filter_upwards [BinaryFraction.computedCoarseInitialWithWork_bound] with N hN
  intro B d x y hB hd hxy hsymbols hinstance draw
  have hb := hN B d x y hB hd hxy hsymbols
    (Nat.pos_of_neZero _) (pow_pos (Nat.two_pow_pos _) _)
    (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) draw
  exact_mod_cast hb

noncomputable def coarseEntryCostSum {M J B : ℕ} [NeZero B] (source target : List ℕ)
    (N : ℕ) (depth : PhysicalEntry M J target.length → ℕ)
    (draw : PhysicalCoarseDraw source target B depth)
    (selected : PhysicalEntry M J target.length → Prop) : ℝ := by
  classical
  exact ∑ entry : PhysicalEntry M J target.length, selectionIndicator (selected entry) *
    (coarseEntryBinaryCost N B (depth entry) (physicalSource source entry.1)
      (substring target entry.2.lo entry.2.hi) (draw entry) : ℝ)

theorem coarseEntryCostSum_bound {M J B : ℕ} [NeZero B] (source target : List ℕ)
    (N : ℕ) (depth : PhysicalEntry M J target.length → ℕ)
    (draw : PhysicalCoarseDraw source target B depth)
    (selected : PhysicalEntry M J target.length → Prop) (C : ℝ)
    (hc : ∀ entry : PhysicalEntry M J target.length,
      (coarseEntryBinaryCost N B (depth entry) (physicalSource source entry.1)
        (substring target entry.2.lo entry.2.hi) (draw entry) : ℝ) ≤
        C * ((coarseInitialArrayWork B (depth entry) (initialThresholdQ N) (initialLambda N)
          (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (draw entry) : ℝ) +
          ((physicalSource source entry.1).length + 1 : ℕ))) :
    coarseEntryCostSum source target N depth draw selected ≤ C *
      ((∑ entry : PhysicalEntry M J target.length, selectionIndicator (selected entry) *
        (coarseInitialArrayWork B (depth entry) (initialThresholdQ N) (initialLambda N)
          (physicalSource source entry.1) (substring target entry.2.lo entry.2.hi) (draw entry) : ℝ)) +
        ∑ entry : PhysicalEntry M J target.length, selectionIndicator (selected entry) *
          ((physicalSource source entry.1).length + 1 : ℕ)) := by
  classical
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  unfold coarseEntryCostSum
  apply Finset.sum_le_sum
  intro entry _
  have hs : 0 ≤ selectionIndicator (selected entry) := by
    unfold selectionIndicator
    split <;> norm_num
  exact (mul_le_mul_of_nonneg_left (hc entry) hs).trans_eq (by ring)

end EditApproximation

end OAI
