import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedInitial
import OAI.Combinatorics.EditApproximation.Coarse.CoarseIndexedOverhead

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseRootReadExtra {B d : ℕ} (k q L : ℕ) (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (x y : List ℕ) (draws : CoarseThresholdDraws B d) : ℕ :=
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  coarseIndexedExtra k q L (coarseEntryWidth x y) x y two.1 d 0 draws allowance.1 0

theorem coarseIndexedRootWithWork_cost_compare {B d : ℕ} (k q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseThresholdDraws B d) :
    (coarseIndexedRootWithWork k q L hB hq hL x y draws).2 ≤
      (coarseRootWithWork k q L hB hq hL
        (coarseTargetFrame k (coarsePadTo (coarseEntryWidth x y) y))
        (coarseEntryTree B d x y) draws 0 (coarseRootShift k)).2 +
        coarseRootReadExtra k q L hB hq hL x y draws := by
  let den := coarseRootDenominator B q L d
  let denPos := coarseRootDenominator_pos B q L d hB hq hL
  let two := coarseGridNatWithWork den.1 denPos 2
  let allowance := coarseGridNatWithWork den.1 denPos k
  have h := coarseIndexedWithWork_cost_compare k q L (coarseEntryWidth x y) x y
    two.1 d 0 draws allowance.1 0
  rw [coarseReadCore_eq k q L (coarseEntryWidth x y) x y (le_max_left _ _) (le_max_right _ _)] at h
  simp only [Nat.zero_add, coarseReadTree_entry] at h
  unfold coarseIndexedRootWithWork coarseRootWithWork coarseRootReadExtra
  change den.2 + two.2 + allowance.2 + _ + 1 ≤ den.2 + two.2 + allowance.2 + _ + 1 + _
  dsimp only [den, denPos, two, allowance] at h ⊢
  omega

theorem coarseIndexedCandidateWithWork_cost_compare {B d : ℕ} (q L : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (i : CoarseGuessIndex (coarseEntryWidth x y)) (draws : CoarseThresholdDraws B d) :
    (coarseIndexedCandidateWithWork q L hB hq hL x y i draws).2 ≤
      (coarseCandidateWithWork q L hB hq hL x y i draws).2 +
        coarseRootReadExtra (coarseGuess (coarseEntryWidth x y) i) q L hB hq hL x y draws := by
  have h := coarseIndexedRootWithWork_cost_compare
    (coarseGuess (coarseEntryWidth x y) i) q L hB hq hL x y draws
  unfold coarseIndexedCandidateWithWork coarseCandidateWithWork
  simp only [coarseIndexedRootWithWork_value]
  omega

end BinaryFraction
end EditApproximation

end OAI
