import OAI.Combinatorics.EditApproximation.Coarse.CoarseInitialBinary
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandGuardWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction



 theorem naturalListEqualWithWork_value (x y : List ℕ) :
    (naturalListEqualWithWork x y).1 = true ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp [naturalListEqualWithWork]
  | cons a left ih =>
    cases y with
    | nil => simp [naturalListEqualWithWork]
    | cons b right =>
      simp only [naturalListEqualWithWork]
      by_cases hab : a = b
      · rw [ite_eq_left ((naturalEqualWithWork_value a b).mpr hab), ih]
        simp only [List.cons.injEq, hab, true_and]
      · have ht : ¬ (naturalEqualWithWork a b).1 = true :=
          fun h => hab ((naturalEqualWithWork_value a b).mp h)
        simp only [ite_eq_right ht, Bool.false_eq_true, List.cons.injEq, hab, false_and]

/-- Entire dyadic initial estimator, including direct cases, every root
execution, binary minimum, ceiling, and final integer clamp. -/
def coarseInitialWithWork {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) : ℕ × ℕ :=
  let long := binaryNaturalCompareWithWork (2 * x.length) y.length
  if long.1 = .lt then (min N y.length, long.2 + Nat.size N + Nat.size y.length + 4) else
  let equal := naturalListEqualWithWork x y
  if equal.1 then (0, long.2 + equal.2 + 3) else
  let roots := arithmeticMapWithWork (fun i => coarseCandidateWithWork q L hB hq hL x y i (draws i))
    (List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1))
  let smallest := coarseMinimumWithWork roots.1
  let rounded := naturalCeilingWithWork smallest.1
  let result := wordMinWithWork N.bits rounded.1
  (bitWordValue result.1, long.2 + equal.2 + roots.2 + smallest.2 + rounded.2 + result.2 +
    Nat.size N + 6)

 theorem coarseInitialWithWork_value {B d : ℕ} (q L N : ℕ)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L) (x y : List ℕ)
    (draws : CoarseGuessIndex (coarseEntryWidth x y) → CoarseThresholdDraws B d) :
    (coarseInitialWithWork q L N hB hq hL x y draws).1 =
      coarseInitialValue B d q (1 / L) N x y draws := by
  unfold coarseInitialWithWork coarseInitialValue
  by_cases hl : 2 * x.length < y.length
  · have hb : (binaryNaturalCompareWithWork (2 * x.length) y.length).1 = Ordering.lt := by
      exact (binaryNaturalCompareWithWork_lt _ _).mpr hl
    simp only [hb, ite_true, ite_eq_left hl]
  · have hb : ¬ (binaryNaturalCompareWithWork (2 * x.length) y.length).1 = Ordering.lt := by
      exact fun h => hl ((binaryNaturalCompareWithWork_lt _ _).mp h)
    rw [ite_eq_right hb, ite_eq_right hl]
    by_cases he : x = y
    · rw [ite_eq_left ((naturalListEqualWithWork_value x y).mpr he), ite_eq_left he]
    · rw [ite_eq_right (fun h => he ((naturalListEqualWithWork_value x y).mp h)), ite_eq_right he]
      dsimp only
      rw [wordMinWithWork_value, bitWordValue_bits, naturalCeilingWithWork_value]
      congr 2
      rw [arithmeticMapWithWork_value]
      have hm : (List.finRange (Nat.clog 2 (coarseEntryWidth x y) + 1)).map
          (fun i => (coarseCandidateWithWork q L hB hq hL x y i (draws i)).1) =
          List.ofFn (fun i => (coarseCandidateWithWork q L hB hq hL x y i (draws i)).1) := by
        rw [List.ofFn_eq_map]
      rw [hm, coarseMinimumWithWork_ofFn]
      simp only [coarseInitialMinimum, coarseCandidateWithWork_value]

end BinaryFraction
end EditApproximation

end OAI
