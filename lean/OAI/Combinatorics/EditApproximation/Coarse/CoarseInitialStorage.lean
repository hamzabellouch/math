import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseHistory
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction
open Filter

def coarseInitialArrayHistory (N B d : ℕ) [NeZero B] (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ :=
  if 2 * x.length < y.length then 0 else if x = y then 0 else
    ∑ i : CoarseGuessIndex (coarseEntryWidth x y),
      coarseRootArrayHistory (coarseGuess (coarseEntryWidth x y) i)
        (inputHeight N ^ 4) (64 * inputHeight N) (Nat.pos_of_neZero B)
        (pow_pos (Nat.two_pow_pos _) _) (Nat.mul_pos (by decide) (Nat.two_pow_pos _))
        (coarseTargetFrame (coarseGuess (coarseEntryWidth x y) i)
          (coarsePadTo (coarseEntryWidth x y) y)) (coarseEntryTree B d x y) (draws i) 0

theorem coarseInitialArrayHistory_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ B d : ℕ, ∀ x y : List ℕ,
      B = (integerParameters N).B → d = computedCoarseDepth N (coarseEntryWidth x y) →
      coarseEntryWidth x y ≤ N → ∀ (_hB : NeZero B)
      (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d),
      coarseInitialArrayHistory N B d x y draws ≤ (N + 2) ^ 37 := by
  filter_upwards [computedCoarseAllHistories_polynomial] with N hN
  intro B d x y hBdef hddef hsize inst draws
  unfold coarseInitialArrayHistory
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact hN B d x y hBdef hddef hsize (Nat.pos_of_neZero B)
      (pow_pos (Nat.two_pow_pos _) _) (Nat.mul_pos (by decide) (Nat.two_pow_pos _)) draws

end BinaryFraction



theorem coarseHistoryKeyCost_le {α β ι : Type*} (cost : ι → ℕ) (C : ℕ)
    (hcost : ∀ entry, cost entry ≤ C) (key : Sum α (Sum ι β)) :
    coarseHistoryKeyCost cost key ≤ C := by
  rcases key with scalar | entry | table
  · exact Nat.zero_le _
  · exact hcost entry
  · exact Nat.zero_le _

theorem coarseHistoryKeysSum_le {α β ι : Type*} (cost : ι → ℕ) (C : ℕ)
    (hcost : ∀ entry, cost entry ≤ C) (keys : List (Sum α (Sum ι β))) :
    (keys.map (coarseHistoryKeyCost cost)).sum ≤ C * keys.length := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have hk := coarseHistoryKeyCost_le cost C hcost key
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

end EditApproximation

end OAI
