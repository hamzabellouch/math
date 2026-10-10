import OAI.Combinatorics.EditApproximation.Refinement.PhysicalFamilyProgram
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomMemoWork

namespace OAI

namespace EditApproximation

section Work

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ) (hPpos : 0 < P)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "group" => physicalFamilyGroup target N P ell exponent H (ell ^ 80) passes copies draw
local notation "integer" => physicalFamilyInteger source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta hPpos draw initial
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw
local notation "bodyValue" => physicalFamilyProgram_value source target N P ell exponent H (ell ^ 80)
  T S passes copies factor multiplier tau eta kappa delta initial hPpos draw

noncomputable def physicalFamilyDependencyTree
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) : DependencyExpansion :=
  chargedRandomDependencyTree source target N P H T S (passes + 1) copies factor multiplier
    tau eta kappa delta group integer initial readGroup readInteger answer bodyValue root

 theorem physicalFamilyDependencyTree_depth
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).depth = root.depth := by
  exact queryDependencyExpansion_depth _ _ _
    (chargedRandomRequestList_progress source target N P H T S (passes + 1) copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger answer bodyValue) root

 theorem physicalFamilyDependencyTree_rank
    (hpasses : passes = computedSeedPassCount N) (hT : T = (integerParameters N).T)
    (hS : S = (integerParameters N).S)
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).rank ≤ computedDependencyIndexCount N := by
  have heq : (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).rank = root.index :=
    queryDependencyExpansion_index _ _ _
      (chargedRandomRequestList_progress source target N P H T S (passes + 1) copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger answer bodyValue) root
  rw [heq]
  apply (chargedRequest_index_le root).trans_eq
  simp only [computedDependencyIndexCount, hpasses, hT, hS]

 theorem physicalFamilyDependencyTree_valid
    (hN : 0 < N) (hell : 200 ≤ ell) (hM : M = (integerParameters N).M)
    (hP : P = (integerParameters N).P) (hT : T = (integerParameters N).T)
    (hS : S = (integerParameters N).S) (hcopies : copies ≤ inputHeight N ^ 2)
    (hAmin : ∀ pass, 1 ≤ factor pass)
    (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw root).Valid
      (M * ell ^ 257) (inputHeight N ^ (512 * (coarseExponent ell + 1))) :=
  chargedRandomDependencyTree_valid source target N P H T S (passes + 1) copies factor multiplier
    tau eta kappa delta group integer initial readGroup readInteger answer bodyValue
    hN hell hM hP hT hS hcopies hAmin hAmax root

 theorem physicalFamilyMemo_requests_le_width
    (hN : 0 < N) (hell : 200 ≤ ell) (hM : M = (integerParameters N).M)
    (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))
    (bits : ℕ) (encode : Sum
      (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
        target N P ell exponent H (ell ^ 80) passes copies)
      (ChargedPhysicalRequest M J target.length (passes + 1) copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (root : ChargedPhysicalRequest M J target.length (passes + 1) copies T S) :
    (chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80) T S (passes + 1)
      copies factor multiplier tau eta kappa delta readGroup readInteger initial answer bits encode root).requests ≤
    (inputHeight N ^ 91 + 1) *
      (physicalFamilyDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta initial hPpos draw root).widthWork M source.length :=
  chargedRandomMemoEvaluate_requests_le_widthWork source target N P H T S (passes + 1)
    copies factor multiplier tau eta kappa delta group integer initial readGroup readInteger answer
    bodyValue (inputHeight N ^ 91) bits encode hinjective hbounded
    (computed_physicalFamilyProgram_source_cost source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial hPpos draw hN hell hM hAmax) root

end Work

end EditApproximation

end OAI
