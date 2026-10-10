import OAI.Combinatorics.EditApproximation.Queries.QueryProgramPolynomial
import OAI.Combinatorics.EditApproximation.Refinement.ComputedPreparedInputBounds
import OAI.Combinatorics.EditApproximation.Refinement.ComputedLocalKernelWork

namespace OAI

namespace EditApproximation
open Filter

/-- Degree of the complete adaptive program when physical reads have degree `K`. -/
def computedQueryProgramDegree (K : ℕ) : ℕ := (K + 1) * (16 * queryLocalProgramBitDegree)

theorem computedQueryProgramBudget_cap (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ t W : ℕ, t ≤ inputHeight N ^ 2 →
      W ≤ computedLocalKernelBudget K N →
      BinaryFraction.queryLocalProgramBitBudget (integerParameters N).M N (integerParameters N).P
        (inputSmallLog N) (40 * smallLogExponent N) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t W ≤
        computedLocalKernelBudget (computedQueryProgramDegree K) N := by
  filter_upwards [computedPreparedNumericBounds,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hn hell
  intro t W ht hW
  let H := inputHeight N
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let p := coarseExponent (inputSmallLog N)
  let L := (100 * M + 100000) * (p + 1)
  let S := H ^ L
  let X := S ^ (K + 1)
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hp : 0 < H := by omega
  have hL : 40 ≤ L := by
    dsimp only [L]
    nlinarith only [Nat.zero_le M, Nat.zero_le p, Nat.zero_le (M * p)]
  have hHS : H ≤ S := Nat.le_pow (by omega)
  have hSX : S ≤ X := Nat.le_pow (by omega)
  have hX : 64 ≤ X := hH.trans (hHS.trans hSX)
  have hz : BinaryFraction.zero.width ≤ H ^ 8 := by
    change 1 ≤ H ^ 8
    exact one_le_pow₀ (by omega)
  have hzv : BinaryFraction.zero.value = 0 := by
    norm_num [BinaryFraction.value, BinaryFraction.zero, SignedBinary.value, signedMagnitude, bitWordValue]
  have hnum := hn 0 0 (by omega) t ht BinaryFraction.zero BinaryFraction.zero
    BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero hz hz hz hz hz
    (by rw [hzv]; simp)
    (by rw [hzv]; norm_num)
    (fun _ _ => 0) (by intro b r; simp)
  change BinaryFraction.PreparedKernelNumericBounds (nx := 0) (ny := 0) (M := M)
    N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (H ^ 8) (H ^ 5) S t
    BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero
    (fun _ _ => 0) at hnum
  have hB : H ^ 8 ≤ S := by have := hnum.wordCap; omega
  have he : 40 * smallLogExponent N ≤ S := by
    have := hnum.thetaSize
    omega
  have heM : heightExponent N / 20 ≤ S := by have := hnum.scaleSizes; omega
  have heF : smallLogExponent N ≤ S := by have := hnum.scaleSizes; omega
  have hTheta : 2 ^ (40 * smallLogExponent N) ≤ S := by
    calc
      _ = inputSmallLog N ^ 40 := by unfold inputSmallLog; rw [← pow_mul]; congr 1; omega
      _ ≤ H ^ 40 := Nat.pow_le_pow_left (computed_smallLog_le_height N) 40
      _ ≤ S := Nat.pow_le_pow_right hp hL
  have hWX : W ≤ X := by
    apply hW.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left L (Nat.le_succ K))
  have h := queryLocalProgramBitBudget_uniform_cap M N P (inputSmallLog N)
    (40 * smallLogExponent N) (heightExponent N / 20) (smallLogExponent N) (H ^ 8) S t W X
    hX hnum.inputSize (hnum.arityCap.trans hSX) (hnum.precisionCap.trans hSX)
    ((computed_smallLog_le_height N).trans (hHS.trans hSX)) (he.trans hSX) (heM.trans hSX)
    (heF.trans hSX) (hB.trans hSX) hSX (hnum.timeCap.trans hSX) hWX
    (hTheta.trans hSX) (hnum.actionCap.trans hSX) (hnum.cartesianCap.trans hSX)
  apply h.trans_eq
  change ((H ^ L) ^ (K + 1)) ^ (16 * queryLocalProgramBitDegree) =
    H ^ (L * computedQueryProgramDegree K)
  rw [← pow_mul, ← pow_mul]
  congr 1

end EditApproximation

end OAI
