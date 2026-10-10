import OAI.Combinatorics.EditApproximation.Refinement.ComputedChargedQueryBudget
import OAI.Combinatorics.EditApproximation.Queries.QueryDependencyCosts
import OAI.Combinatorics.EditApproximation.Geometry.DependencyWeightedWork

namespace OAI

/-! The dependency expansion is built from the charged evaluator's
executed requests. Its branching bounds therefore apply to actual lazy
evaluation, with coarse leaves at their original physical depths. -/

namespace EditApproximation

theorem chargedRequest_index_le {M J ny passes copies T S : ℕ}
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    request.index ≤ passes * (T + S + 1) := by
  cases request with
  | inl entry => exact Nat.zero_le _
  | inr parent =>
    have hp : parent.val.pass + 1 ≤ passes := parent.property.1
    have hi : parent.val.index + 1 ≤ T + S + 1 := Nat.add_le_add_right parent.property.2.2 1
    change parent.val.pass * (T + S + 1) + parent.val.index + 1 ≤ _
    calc
      _ ≤ (parent.val.pass + 1) * (T + S + 1) := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hp

section Expansion

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "program" => chargedGlobalQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta group integer initial
local notation "values" => chargedRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta group integer initial
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

 theorem chargedRequestList_progress (root child : ChargedPhysicalRequest M J target.length passes copies T S)
    (hchild : child ∈ queryRequestList depth index program root) :
    (depth child < depth root ∧ index child ≤ index root) ∨
      (depth child ≤ depth root ∧ index child < index root) := by
  have hvalue := rankedProgramValue_eq ChargedPhysicalRequest.rank program values
    (chargedGlobalQuery_value source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta group integer initial)
  change child ∈ ((program root).keys
    (fun key => rankedProgramValue ChargedPhysicalRequest.rank program key.val)).map Subtype.val at hchild
  simp only [hvalue] at hchild
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hchild
  exact chargedGlobalQuery_keys_progress source target N P (inputSmallLog N) (40 * smallLogExponent N)
    H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta group integer initial root key hk

 def chargedDependencyTree (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    DependencyExpansion :=
  queryDependencyExpansion depth index program
    (chargedRequestList_progress source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial) root

variable (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
  (hT : T = (integerParameters N).T) (hS : S = (integerParameters N).S)
  (hcopies : copies ≤ inputHeight N ^ 2)
  (hAmin : ∀ pass, 1 ≤ factor pass)
  (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))

include hN hell hM hP hT hS hcopies hAmin hAmax in
 theorem chargedDependencyTree_valid (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial root).Valid
      (M * inputSmallLog N ^ 257)
      (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) := by
  apply queryDependencyExpansion_valid
  · intro key
    rw [querySameRequests_length_eq_cost depth index program values
      (chargedGlobalQuery_value source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta group integer initial)]
    have h := computed_chargedGlobalQuery_current_reads source target N P H T S passes copies
      factor multiplier tau eta kappa delta group integer initial hN hell hM hAmax key
    apply h.trans
    calc
      2 * M * inputSmallLog N ^ 256 ≤ inputSmallLog N * M * inputSmallLog N ^ 256 := by
        gcongr
        omega
      _ = M * inputSmallLog N ^ 257 := by ring
  · intro key
    rw [queryEarlierRequests_length_eq_cost depth index program values
      (chargedGlobalQuery_value source target N P (inputSmallLog N) (40 * smallLogExponent N)
        H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta group integer initial)]
    exact computed_chargedGlobalQuery_earlier_reads source target N P H T S passes copies
      factor multiplier tau eta kappa delta group integer initial hN hell hM hAmax hP hT hS hcopies hAmin key


include hN hell hM hP hT hS hcopies hAmin hAmax in
 theorem chargedDependencyTree_widthWork_le
    (hJ : J = intervalTreeDepth M source.length)
    (hpasses : passes = computedSeedPassCount N + 1)
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (hroot : depth root = J) (overhead : ℝ) (hoverhead : 0 ≤ overhead)
    (hpath : ∀ j ≤ intervalTreeDepth M source.length,
      (dependencyPathBudget j (computedDependencyIndexCount N)
        (M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) : ℝ) ≤
        (M : ℝ) ^ j * overhead) :
    ((chargedDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial root).widthWork M source.length : ℝ) ≤
      (((intervalTreeDepth M source.length + 1) * source.length +
        4 * M * max 1 source.length : ℕ) : ℝ) * overhead := by
  apply DependencyExpansion.widthWork_le M source.length _ _ (computedDependencyIndexCount N)
    (by rw [hM]; exact (computed_branching_bounds N hN hell).1) _
    (chargedDependencyTree_valid source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial hN hell hM hP hT hS hcopies hAmin hAmax root)
  · exact (queryDependencyExpansion_depth depth index program
      (chargedRequestList_progress source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial) root).trans (hroot.trans hJ)
  · have hi := chargedRequest_index_le root
    have hb : index root ≤ computedDependencyIndexCount N := by
      apply hi.trans_eq
      unfold computedDependencyIndexCount
      rw [hpasses, hT, hS]
    exact (queryDependencyExpansion_index depth index program
      (chargedRequestList_progress source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial) root).le.trans hb
  · exact hoverhead
  · exact hpath

end Expansion

end EditApproximation

end OAI
