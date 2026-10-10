import OAI.Combinatorics.EditApproximation.Refinement.ComputedChargedRandomBudget
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomProgress
import OAI.Combinatorics.EditApproximation.Geometry.ChargedQueryAsymptotics
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedWork

namespace OAI

namespace EditApproximation

section Expansion

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)

local notation "mixedProgram" => chargedRandomGlobalQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta readGroup readInteger initial
local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank mixedProgram sourceAnswer
local notation "values" => chargedRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta group integer initial
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

variable (hbody : ∀ (request : ChargedPhysicalRequest M J target.length passes copies T S),
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial request).value
    (Sum.elim sourceAnswer (fun child : {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank} => chargedRequestValue source target N P (inputSmallLog N)
        (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
        tau eta kappa delta group integer initial child.val)) =
    chargedRequestValue source target N P (inputSmallLog N)
      (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
      tau eta kappa delta group integer initial request)

include hbody

 theorem chargedRandomRequestList_progress (root child : ChargedPhysicalRequest M J target.length passes copies T S)
    (hchild : child ∈ queryRequestList depth index program root) :
    (depth child < depth root ∧ index child ≤ index root) ∨
      (depth child ≤ depth root ∧ index child < index root) := by
  have hvalue := rankedProgramValue_eq ChargedPhysicalRequest.rank program values
    (SourceRanked.projectedBody_value ChargedPhysicalRequest.rank mixedProgram sourceAnswer values hbody)
  change child ∈ ((program root).keys
    (fun key => rankedProgramValue ChargedPhysicalRequest.rank program key.val)).map Subtype.val at hchild
  simp only [hvalue] at hchild
  obtain ⟨key, hk, rfl⟩ := List.mem_map.mp hchild
  apply FiniteQuery.eraseSources_keys_all sourceAnswer
    (fun child => values child.val) (mixedProgram root)
    (fun child => ChargedPhysicalRequest.DependencyProgress root child.val) ?_ key hk
  intro next hn
  have hp := chargedRandomGlobalQuery_keys_progress source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial sourceAnswer values root next hn
  cases next <;> exact hp

 noncomputable def chargedRandomDependencyTree (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    DependencyExpansion :=
  queryDependencyExpansion depth index program
    (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root

variable (hN : 0 < N) (hell : 200 ≤ inputSmallLog N)
  (hM : M = (integerParameters N).M) (hP : P = (integerParameters N).P)
  (hT : T = (integerParameters N).T) (hS : S = (integerParameters N).S)
  (hcopies : copies ≤ inputHeight N ^ 2)
  (hAmin : ∀ pass, 1 ≤ factor pass)
  (hAmax : ∀ pass, factor pass ≤ ((integerParameters N).initialFactor : ℚ))

include hN hell hM hP hT hS hcopies hAmin hAmax in
 theorem chargedRandomDependencyTree_valid (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).Valid
      (M * inputSmallLog N ^ 257)
      (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) := by
  apply queryDependencyExpansion_valid
  · intro key
    rw [querySameRequests_length_eq_cost depth index program values
      (SourceRanked.projectedBody_value ChargedPhysicalRequest.rank mixedProgram sourceAnswer values hbody)]
    change (FiniteQuery.eraseSources sourceAnswer (mixedProgram key)).cost
      (fun child => values child.val) (fun child => chargedSameWeight key child.val) ≤ _
    rw [FiniteQuery.eraseSources_cost]
    have h := computed_chargedRandomGlobalQuery_current_reads source target N P H T S passes copies
      factor multiplier tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hN hell hM hAmax hP hT hS key
    apply h.trans
    calc
      2 * M * inputSmallLog N ^ 256 ≤ inputSmallLog N * M * inputSmallLog N ^ 256 := by
        gcongr
        omega
      _ = M * inputSmallLog N ^ 257 := by ring
  · intro key
    rw [queryEarlierRequests_length_eq_cost depth index program values
      (SourceRanked.projectedBody_value ChargedPhysicalRequest.rank mixedProgram sourceAnswer values hbody)]
    change (FiniteQuery.eraseSources sourceAnswer (mixedProgram key)).cost
      (fun child => values child.val) (fun child => chargedEarlierWeight key child.val) ≤ _
    rw [FiniteQuery.eraseSources_cost]
    exact computed_chargedRandomGlobalQuery_earlier_reads source target N P H T S passes copies
      factor multiplier tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hN hell hM hAmax hP hT hS hcopies hAmin key


include hN hell hM hP hT hS hcopies hAmin hAmax in
 theorem chargedRandomDependencyTree_widthWork_le
    (hJ : J = intervalTreeDepth M source.length)
    (hpasses : passes = computedSeedPassCount N + 1)
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (hroot : depth root = J) (overhead : ℝ) (hoverhead : 0 ≤ overhead)
    (hpath : ∀ j ≤ intervalTreeDepth M source.length,
      (dependencyPathBudget j (computedDependencyIndexCount N)
        (M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) : ℝ) ≤
        (M : ℝ) ^ j * overhead) :
    ((chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork M source.length : ℝ) ≤
      (((intervalTreeDepth M source.length + 1) * source.length +
        4 * M * max 1 source.length : ℕ) : ℝ) * overhead := by
  apply DependencyExpansion.widthWork_le M source.length _ _ (computedDependencyIndexCount N)
    (by rw [hM]; exact (computed_branching_bounds N hN hell).1) _
    (chargedRandomDependencyTree_valid source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody hN hell hM hP hT hS hcopies hAmin hAmax root)
  · exact (queryDependencyExpansion_depth depth index program
      (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root).trans (hroot.trans hJ)
  · have hi := chargedRequest_index_le root
    have hb : index root ≤ computedDependencyIndexCount N := by
      apply hi.trans_eq
      unfold computedDependencyIndexCount
      rw [hpasses, hT, hS]
    exact (queryDependencyExpansion_index depth index program
      (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root).le.trans hb
  · exact hoverhead
  · exact hpath

end Expansion

end EditApproximation

end OAI
