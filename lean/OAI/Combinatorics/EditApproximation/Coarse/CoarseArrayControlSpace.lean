import OAI.Combinatorics.EditApproximation.Coarse.CoarseScalarControlSpace
import OAI.Combinatorics.EditApproximation.Coarse.CoarseArrayAllocation

namespace OAI

namespace EditApproximation
namespace BinaryFraction

def coarseGridScanInvocations (two previous : BinaryFraction) : List BinaryFraction → ℕ
  | [] => 1
  | head :: rest =>
    let added := coarseGridAddWithWork previous two
    let next := minWithWork head added.1
    coarseGridAddInvocations previous two + compareInvocations head added.1 +
      coarseGridScanInvocations two next.1 rest + 2

theorem coarseGridScanInvocations_le_work (two previous : BinaryFraction) (source : List BinaryFraction) :
    coarseGridScanInvocations two previous source ≤ (coarseGridScanWithWork two previous source).2 + 1 := by
  induction source generalizing previous with
  | nil => rfl
  | cons head rest ih =>
    have ha := coarseGridAddInvocations_le_work previous two
    have hm := compareInvocations_le_work head (coarseGridAddWithWork previous two).1
    have ht := ih (minWithWork head (coarseGridAddWithWork previous two).1).1
    simp only [coarseGridScanInvocations, coarseGridScanWithWork]
    simp only [minWithWork] at ht ⊢
    omega

def coarseGridLeftInvocations (two : BinaryFraction) : List BinaryFraction → ℕ
  | [] => 1
  | head :: rest => coarseGridScanInvocations two head rest + 1

theorem coarseGridLeftInvocations_le_work (two : BinaryFraction) (source : List BinaryFraction) :
    coarseGridLeftInvocations two source ≤ (coarseGridLeftWithWork two source).2 + 2 := by
  cases source with
  | nil => simp [coarseGridLeftInvocations, coarseGridLeftWithWork]
  | cons head rest =>
    have h := coarseGridScanInvocations_le_work two head rest
    simp only [coarseGridLeftInvocations, coarseGridLeftWithWork]
    omega

def coarseGridZipMinimumInvocations : List BinaryFraction → List BinaryFraction → ℕ
  | a :: left, b :: right => compareInvocations a b + coarseGridZipMinimumInvocations left right + 2
  | _, _ => 1

theorem coarseGridZipMinimumInvocations_le_work (left right : List BinaryFraction) :
    coarseGridZipMinimumInvocations left right ≤ (coarseGridZipMinimumWithWork left right).2 + 1 := by
  induction left generalizing right with
  | nil => exact Nat.le_refl 1
  | cons a left ih =>
    cases right with
    | nil => exact Nat.le_refl 1
    | cons b right =>
      have hh := compareInvocations_le_work a b
      have ht := ih right
      simp only [coarseGridZipMinimumInvocations, coarseGridZipMinimumWithWork, minWithWork]
      omega

/-- Includes one invocation per reverse-list step, even if implemented with
an iterative constant-stack loop. -/
def coarseGridPenaltyInvocations (two : BinaryFraction) (source : List BinaryFraction) : ℕ :=
  let left := coarseGridLeftWithWork two source
  let right := coarseGridLeftWithWork two source.reverse
  coarseGridLeftInvocations two source + coarseGridLeftInvocations two source.reverse +
    source.length + right.1.length + coarseGridZipMinimumInvocations left.1 right.1.reverse + 3

theorem coarseGridPenaltyInvocations_le_work (two : BinaryFraction) (source : List BinaryFraction) :
    coarseGridPenaltyInvocations two source ≤ 2 * (coarseGridPenaltyWithWork two source).2 + 8 := by
  have hl := coarseGridLeftInvocations_le_work two source
  have hr := coarseGridLeftInvocations_le_work two source.reverse
  have hz := coarseGridZipMinimumInvocations_le_work
    (coarseGridLeftWithWork two source).1 (coarseGridLeftWithWork two source.reverse).1.reverse
  have hlen := coarseGridLeftWithWork_length two source.reverse
  simp only [List.length_reverse] at hr hlen
  unfold coarseGridPenaltyInvocations coarseGridPenaltyWithWork
  dsimp only
  rw [hlen]
  omega

def coarseGridZipAddInvocations : List BinaryFraction → List BinaryFraction → ℕ
  | a :: left, b :: right => coarseGridAddInvocations a b + coarseGridZipAddInvocations left right + 1
  | _, _ => 1

theorem coarseGridZipAddInvocations_le_work (left right : List BinaryFraction) :
    coarseGridZipAddInvocations left right ≤ (coarseGridZipAddWithWork left right).2 + 1 := by
  induction left generalizing right with
  | nil => exact Nat.le_refl 1
  | cons a left ih =>
    cases right with
    | nil => exact Nat.le_refl 1
    | cons b right =>
      have hh := coarseGridAddInvocations_le_work a b
      have ht := ih right
      simp only [coarseGridZipAddInvocations, coarseGridZipAddWithWork]
      omega

def coarseBinaryAddInvocations : CoarseBinaryArray → CoarseBinaryArray → ℕ
  | some left, some right => coarseGridZipAddInvocations left right + 1
  | _, _ => 1

theorem coarseBinaryAddInvocations_le_work (left right : CoarseBinaryArray) :
    coarseBinaryAddInvocations left right ≤ (coarseBinaryAddWithWork left right).2 + 2 := by
  cases left <;> cases right
  all_goals first | exact (by decide : 1 ≤ 2) |
    exact Nat.add_le_add_right (coarseGridZipAddInvocations_le_work _ _) 1

def coarseBinaryPenaltyInvocations (two : BinaryFraction) : CoarseBinaryArray → ℕ
  | none => 1
  | some values => coarseGridPenaltyInvocations two values + 1

theorem coarseBinaryPenaltyInvocations_le_work (two : BinaryFraction) (array : CoarseBinaryArray) :
    coarseBinaryPenaltyInvocations two array ≤ 2 * (coarseBinaryPenaltyWithWork two array).2 + 9 := by
  cases array with
  | none => exact (by decide : 1 ≤ 9)
  | some values => exact Nat.add_le_add_right (coarseGridPenaltyInvocations_le_work two values) 1

def coarseBinaryMapInvocations (invocations : BinaryFraction → ℕ) : CoarseBinaryArray → ℕ
  | none => 1
  | some values => arithmeticMapInvocations invocations values + 1

theorem coarseBinaryMapInvocations_le_work (f : BinaryFraction → BinaryFraction × ℕ)
    (invocations : BinaryFraction → ℕ) (h : ∀ a, invocations a ≤ (f a).2) (array : CoarseBinaryArray) :
    coarseBinaryMapInvocations invocations array ≤ (coarseBinaryMapWithWork f array).2 + 2 := by
  cases array with
  | none => exact (by decide : 1 ≤ 2)
  | some values =>
    exact Nat.add_le_add_right
      (arithmeticMapInvocations_le_work f invocations values (fun a _ => h a)) 1

end BinaryFraction
end EditApproximation

end OAI
