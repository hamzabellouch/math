import OAI.Combinatorics.EditApproximation.Queries.QueryChargedFamilySpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryNormalizationSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryFamilyMemo

namespace OAI

namespace EditApproximation
open BitQuery

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (allocation : PhysicalEntry M J target.length → ℕ)
  (hc : ∀ entry, allocation entry ≤ 3 * (coarse entry).2)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)

def queryFamilyMemoRawHeap
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes)
      (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
    Heap (queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw key) := by
  cases key with
  | inl scalar =>
    exact Heap.computeOf (queryFamilySourceWordWithWork target N P F exponent H Q draw scalar)
      (Nat.size (draw scalar).val + 2) (by simp only [queryFamilySourceWordWithWork]; omega)
  | inr request =>
    exact (queryChargedFamilyGlobalHeap source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation hc request).mapKeysWithWork
        _ (fun _ => 1) (fun _ => le_rfl)

def queryFamilyMemoNormalizedHeap (base : List Bool) (hbase : 0 < bitWordValue base)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes)
      (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
    Heap (queryFamilyMemoNormalized source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw base hbase key) :=
  (queryFamilyMemoRawHeap source target N P F exponent H Q eM eF hP hM hF
    A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation hc draw key).normalize
      base hbase (queryFamilyMemoRemaining target N P F exponent H Q key)

end Family
end EditApproximation

end OAI
