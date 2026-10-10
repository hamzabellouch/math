import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseCardinalRounding
import OAI.Combinatorics.KMedian.Sparse.SparseSupport
import OAI.Combinatorics.KMedian.Sparse.SparseNonnegativeSupport

namespace OAI

section
section
namespace MetricKMedian.SparseWeightedPartial
open RationalWeightedStep

theorem run_positive {n : ℕ} (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (t : ℕ) (a : Fin (run β hβ p t).length) :
    0 < (run β hβ p t).law.rational.weight a := by
  cases t with
  | zero => change 0 < ((1:ℤ):ℚ)/1; norm_num
  | succ t =>
    exact ((run β hβ p t).branch (probability β) (probability_unit β hβ)
      (endpoint β)).compressAuto_positive features a

end MetricKMedian.SparseWeightedPartial

namespace MetricKMedian.SparseCardinalRounding
open RationalWeightedStep

theorem zero_fixed {n : ℕ} (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1) (i : Fin n) (hi : point p i=0)
    (a : Fin (round p).length) : point (round p).states[a.val] i=0 := by
  apply SparseIntegerLaw.zero_nonnegative (round p) (fun q => point q i)
    (fun b => ((SparseWeightedPartial.run_invariants (fun _ => 1)
      (fun _ => by norm_num) p hp n b).1 i).1)
    ((round_mean p i).trans hi) a
    (SparseWeightedPartial.run_positive _ _ _ _ a)

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
