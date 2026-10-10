import OAI.Combinatorics.EditApproximation.Queries.QueryChargedFamily
import OAI.Combinatorics.EditApproximation.Binary.BitSourceRanked
import OAI.Combinatorics.EditApproximation.Binary.BitRankedNormalize
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRequestGrid
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! One binary memo stores independent scalar draws, coarse values, and
all recursive tables.  The raw implementation preserves the exact
reference trace; normalization is justified on its reachable values. -/

namespace EditApproximation

section Family
variable {M J R passes copies T S : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (A a : ℕ → BinaryFraction) (tau eta kappa delta : BinaryFraction) (multiplier : ℕ → ℕ)
  (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
  (coarse : PhysicalEntry M J target.length → BinaryFraction × ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)





def queryFamilyMemoRaw (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :=
  SourceRanked.bitBody ChargedPhysicalRequest.rank
    (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse)
    (queryFamilySourceWordWithWork target N P F exponent H Q draw) key

theorem queryFamilyMemoRaw_refines
    (ha : ∀ pass, pass ≤ passes → (a pass).value = refinementFactor (A pass).value F)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (initial : PhysicalEntry M J target.length → ℕ)
    (hc : ∀ entry, (coarse entry).1.value = initial entry)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
        A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw key)
      (SourceRanked.body ChargedPhysicalRequest.rank
        (physicalFamilyProgram source target N P F exponent H Q T S passes copies
          (fun pass => (A pass).value) multiplier tau.value eta.value kappa.value delta.value initial)
        (physicalFamilyAnswer target N P F exponent H Q passes copies draw) key) := by
  have hr := SourceRanked.bitBody_refines ChargedPhysicalRequest.rank
    (queryChargedFamilyGlobal (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse)
    (physicalFamilyProgram source target N P F exponent H Q T S passes copies
      (fun pass => (A pass).value) multiplier tau.value eta.value kappa.value delta.value initial)
    (queryFamilySourceWordWithWork target N P F exponent H Q draw)
    (fun parent => queryChargedFamilyGlobal_refines source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits ha hs ht hp htable
      coarse initial hc parent) key
  have hsources : (fun key => (queryFamilySourceWordWithWork target N P F exponent H Q draw key).1.value) =
      physicalFamilyAnswer target N P F exponent H Q passes copies draw := by
    funext key
    exact BinaryFraction.nat_value _
  rw [hsources] at hr
  exact hr



def queryFamilyMemoNormalized (base : List Bool) (hbase : 0 < bitWordValue base)
    (key : QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) :=
  rankedNormalizeBody (SourceRanked.rank ChargedPhysicalRequest.rank)
    (queryFamilyMemoRaw source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse draw)
    base hbase (queryFamilyMemoRemaining (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) key

end Family
end EditApproximation

end OAI
