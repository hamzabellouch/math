import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedArrayHistory
import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialStorage

namespace OAI

namespace EditApproximation
namespace BinaryFraction
open Filter

def coarseIndexedRootArrayHistory {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) : ℕ :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := (coarseGridNatWithWork den.1 denPos 2).1
  let allowance := (coarseGridNatWithWork den.1 denPos k).1
  coarseIndexedArrayHistory k q L (coarseEntryWidth x y) x y two d 0 draws allowance 0

theorem coarseIndexedRootArrayHistory_eq {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) :
    coarseIndexedRootArrayHistory k q L hB hq hL x y draws =
      coarseRootArrayHistory k q L hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 := by
  unfold coarseIndexedRootArrayHistory coarseRootArrayHistory
  dsimp only
  rw [coarseIndexedArrayHistory_eq k q L (coarseEntryWidth x y) x y
    (le_max_left _ _) (le_max_right _ _)]
  simp only [Nat.zero_add, coarseReadTree_entry]

def coarseIndexedInitialArrayHistory (N B d : ℕ) [NeZero B] (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ :=
  if 2 * x.length < y.length then 0 else if x = y then 0 else
    ∑ i : CoarseGuessIndex (coarseEntryWidth x y),
      coarseIndexedRootArrayHistory (coarseGuess (coarseEntryWidth x y) i)
        (inputHeight N ^ 4) (64 * inputHeight N) (Nat.pos_of_neZero B)
        (pow_pos (Nat.two_pow_pos _) _) (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) x y (draws i)

theorem coarseIndexedInitialArrayHistory_eq (N B d : ℕ) [NeZero B] (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    coarseIndexedInitialArrayHistory N B d x y draws = coarseInitialArrayHistory N B d x y draws := by
  unfold coarseIndexedInitialArrayHistory coarseInitialArrayHistory
  split
  · rfl
  · split
    · rfl
    · apply Finset.sum_congr rfl
      intro i _
      exact coarseIndexedRootArrayHistory_eq _ _ _ _ _ _ x y (draws i)

theorem coarseIndexedInitialArrayHistory_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → ∀ (_hB : NeZero B)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      coarseIndexedInitialArrayHistory N B d x y draws ≤ (N + 2) ^ 37 := by
  filter_upwards [coarseInitialArrayHistory_polynomial] with N hN
  intro B d x y hB hd hsize inst draws
  rw [coarseIndexedInitialArrayHistory_eq]
  exact hN B d x y hB hd hsize inst draws

end BinaryFraction
end EditApproximation

end OAI
