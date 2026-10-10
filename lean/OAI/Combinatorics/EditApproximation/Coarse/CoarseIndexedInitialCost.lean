import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedRootCost

namespace OAI

namespace EditApproximation
namespace BinaryFraction

attribute [local irreducible] coarseIndexedCandidateWithWork coarseCandidateWithWork coarseRootReadExtra
  arithmeticMapWithWork coarseMinimumWithWork naturalCeilingWithWork wordMinWithWork

theorem arithmeticMapWithWork_cost_compare {α β : Type*} (f g : α → β × ℕ)
    (extra : α → ℕ) (xs : List α) (hc : ∀ a ∈ xs, (f a).2 ≤ (g a).2 + extra a) :
    (arithmeticMapWithWork f xs).2 ≤ (arithmeticMapWithWork g xs).2 + (xs.map extra).sum := by
  induction xs with
  | nil => simp only [arithmeticMapWithWork, List.map_nil, List.sum_nil, Nat.add_zero, le_refl]
  | cons a xs ih =>
    have ha := hc a List.mem_cons_self
    have hr := ih (fun a ha => hc a (List.mem_cons_of_mem _ ha))
    simp only [arithmeticMapWithWork, List.map_cons, List.sum_cons]
    omega

def coarseInitialReadExtra {B d : ℕ} (q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (x y : List ℕ) (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ :=
  if (binaryNaturalCompareWithWork (2 * x.length) y.length).1 = .lt then 0 else
  if (naturalListEqualWithWork x y).1 then 0 else
  ((List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map fun i =>
    coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i) q L hB hq hL x y (draws i)).sum

theorem coarseIndexedInitialWithWork_cost_compare {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    (coarseIndexedInitialWithWork q L N hB hq hL x y draws).2 ≤
      (coarseInitialWithWork q L N hB hq hL x y draws).2 +
        coarseInitialReadExtra q L hB hq hL x y draws := by
  let indices := List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)
  let f := fun i => coarseIndexedCandidateWithWork q L hB hq hL x y i (draws i)
  let g := fun i => coarseCandidateWithWork q L hB hq hL x y i (draws i)
  let extra := fun i => coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i)
    q L hB hq hL x y (draws i)
  have hc := arithmeticMapWithWork_cost_compare f g extra indices
    (fun i _ => coarseIndexedCandidateWithWork_cost_compare q L hB hq hL x y i (draws i))
  have hv : (arithmeticMapWithWork f indices).1 = (arithmeticMapWithWork g indices).1 := by
    simp only [arithmeticMapWithWork_value, f, g, coarseIndexedCandidateWithWork_value]
  unfold coarseIndexedInitialWithWork coarseInitialWithWork coarseInitialReadExtra
  dsimp only
  split_ifs
  · omega
  · omega
  · dsimp only [f, g, extra, indices] at hc hv
    rw [hv]
    omega

end BinaryFraction
end EditApproximation

end OAI
