import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseSignedRounding
import OAI.Combinatorics.KMedian.Sparse.SparseNonnegativeSupport
import OAI.Combinatorics.KMedian.Sparse.SparseAffineMoments

namespace OAI

section
section
namespace MetricKMedian.SparseSignedRounding
open Finset
open RationalWeightedStep (point fractional)
open SparseWeightedPartial (features)
variable {n : ℕ}

theorem positive (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (a : Fin (round u p hp).length) : 0 < (round u p hp).law.rational.weight a := by
  exact ((SparseSignedPartial.run u p n).bindIndexed (kernel u p hp)).compressAuto_positive features a

theorem fixed (u : Fin n → ℚ) (p : Vector ℚ n)
    (hp : ∀ i, 0 ≤ point p i ∧ point p i ≤ 1)
    (hu : ∀ i, 0 < u i → u i ≤ 1) (e : Fin n)
    (he : point p e=0 ∨ point p e=1) (a : Fin (round u p hp).length) :
    point (round u p hp).states[a.val] e=point p e := by
  rcases he with he | he
  · rw [he]
    apply SparseIntegerLaw.zero_nonnegative (round u p hp) (fun q => point q e)
      (fun i => ((round_invariants u p hp hu i).1 e).1)
      ((round_mean u p hp e).trans he) a (positive u p hp a)
  · have hh : (round u p hp).moment (fun q => 1-point q e)=0 := by
      rw [SparseIntegerLaw.moment_sub,SparseIntegerLaw.moment_const,round_mean,he,sub_self]
    have hz := SparseIntegerLaw.zero_nonnegative (round u p hp) (fun q => 1-point q e)
      (fun i => sub_nonneg.mpr ((round_invariants u p hp hu i).1 e).2)
      hh a (positive u p hp a)
    rw [he]
    linarith only [hz]

end MetricKMedian.SparseSignedRounding
end
end

end OAI
