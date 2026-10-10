import OAI.Combinatorics.EditApproximation.Refinement.PhysicalScalarReadCost
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomMemo
import OAI.Combinatorics.EditApproximation.Refinement.ComputedChargedRandomSourceCost
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The actual scalar family supplies the body-value and source-read
bounds required by the mixed source/table dependency analysis. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)



variable (hP : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P F exponent H Q passes copies)

noncomputable def physicalFamilyRequestValue :=
  chargedRequestValue source target N P F exponent H Q T S (passes + 1) copies
    factor multiplier tau eta kappa delta
    (physicalFamilyGroup target N P F exponent H Q passes copies draw)
    (physicalFamilyInteger source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta hP draw initial) initial

 theorem physicalFamilyProgram_value
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyProgram source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta initial request).value
      (Sum.elim (physicalFamilyAnswer target N P F exponent H Q passes copies draw)
        (fun child => physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta initial hP draw child.val)) =
    physicalFamilyRequestValue source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta initial hP draw request := by
  exact chargedRandomGlobalQuery_value source target N P F exponent H Q T S (passes + 1)
    copies factor multiplier tau eta kappa delta _ _ initial _ _ _
    (physicalRandomBoundedQuery_localValue source target N P F exponent H Q T S (passes + 1)
      copies factor multiplier tau eta kappa delta _ _ initial _ _ _
      (physicalFamilyGroupRead_value target N P F exponent H Q passes copies draw)
      (physicalFamilyOnlineRead_value source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta hP draw initial)) request

end Program

section ComputedCost

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hP : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H
      (inputSmallLog N ^ 80) passes copies)

 theorem computed_physicalFamilyProgram_source_cost
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hM : M = (integerParameters N).M)
    (hA : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (request : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyProgram source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta initial request).cost
      (Sum.elim (physicalFamilyAnswer target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) passes copies draw)
        (fun child => physicalFamilyRequestValue source target N P (inputSmallLog N)
          (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta initial hP draw child.val))
      (Sum.elim (fun _ => 1) (fun _ => 0)) ≤ inputHeight N ^ 91 := by
  have hg := physicalFamilyGroupRead_cost_le target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies
    (physicalFamilyAnswer target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) passes copies draw) (fun _ => 1) 1 (fun _ => le_rfl)
  have ho := physicalFamilyOnlineRead_cost_le target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies
    (physicalFamilyAnswer target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) passes copies draw) (fun _ => 1) 1 (fun _ => le_rfl)
  simpa only [physicalFamilyProgram, physicalFamilyRequestValue, Nat.mul_one] using
    (computed_chargedRandomGlobalQuery_source_cost source target N P H T S (passes + 1) copies
      factor multiplier tau eta kappa delta
      (physicalFamilyGroup target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) passes copies draw)
      (physicalFamilyInteger source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta hP draw initial)
      initial _ _ _ (fun _ => 1) 1 hN hell hM hA hg ho request)

end ComputedCost

end EditApproximation

end OAI
