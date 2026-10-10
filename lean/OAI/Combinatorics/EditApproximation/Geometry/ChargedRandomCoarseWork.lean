import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomCoarseOracle
import OAI.Combinatorics.EditApproximation.Queries.QueryWeightedWork
import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomExpansion
import OAI.Combinatorics.EditApproximation.Probability.FreshCoordinateCost

namespace OAI

namespace EditApproximation

section Coarse

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    GroupScalarKey M (inputSmallLog N) (inputSmallLog N ^ 80) → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)

local notation "program" => SourceRanked.projectedBody ChargedPhysicalRequest.rank
  (chargedRandomGlobalQuery source target N P (inputSmallLog N)
    (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger initial) sourceAnswer
local notation "coarse" => chargedRandomCoarseQuery source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta readGroup readInteger sourceAnswer
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

 theorem chargedRandomCoarseQuery_cost_le (weight : ℕ → ℕ)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (coarse root).cost (fun entry => (initial entry : ℚ))
      (fun entry => weight (J - entry.1.1.val)) ≤
    rankedUncachedWork ChargedPhysicalRequest.rank program (fun request => weight (depth request)) root := by
  have hall : ∀ level root, root.rank = level →
      (coarse root).cost (fun entry => (initial entry : ℚ))
        (fun entry => weight (J - entry.1.1.val)) ≤
      rankedUncachedWork ChargedPhysicalRequest.rank program (fun request => weight (depth request)) root := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro root hlevel
      cases root with
      | inl entry =>
        rw [chargedRandomCoarseQuery, rankedUncachedWork]
        simp only [FiniteQuery.cost, SourceRanked.projectedBody, chargedRandomGlobalQuery, FiniteQuery.eraseSources, ChargedPhysicalRequest.depth, Nat.zero_add,
          Nat.add_zero, le_refl]
      | inr parent =>
        rw [chargedRandomCoarseQuery, FiniteQuery.substitute_cost]
        have hv (child) := chargedRandomCoarseQuery_value source target N P (inputSmallLog N)
          (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger sourceAnswer initial child
        simp_rw [hv]
        unfold SourceRanked.projectedBody
        rw [chargedRandomGlobalQuery_table_initial_independent source target N P (inputSmallLog N)
          (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
          tau eta kappa delta readGroup readInteger (fun _ => 0) initial parent]
        rw [rankedUncachedWork]
        apply (FiniteQuery.cost_mono_weights _ _ _ _ ?_).trans (Nat.le_add_right _ _)
        intro child
        exact ih child.val.rank (hlevel ▸ child.property) child.val rfl
  exact hall root.rank root rfl

variable
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    CellGroupDraws M (inputSmallLog N) (inputSmallLog N ^ 80))
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)

local notation "values" => chargedRequestValue source target N P (inputSmallLog N)
  (40 * smallLogExponent N) H (inputSmallLog N ^ 80) T S passes copies factor multiplier
  tau eta kappa delta group integer initial

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
 theorem chargedRandomCoarseQuery_width_cost_le
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (hroot : depth root = J) :
    (coarse root).cost (fun entry => (initial entry : ℚ))
      (fun entry => 1 + source.length ⌈/⌉ M ^ entry.1.1.val) ≤
    (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork M source.length := by
  have hweight := chargedRandomCoarseQuery_cost_le source target N P H T S passes copies
    factor multiplier tau eta kappa delta readGroup readInteger sourceAnswer initial
    (fun d => 1 + source.length ⌈/⌉ M ^ (J - d)) root
  have hdepth : ∀ entry : PhysicalEntry M J target.length,
      J - (J - entry.1.1.val) = entry.1.1.val := by
    intro entry
    have := entry.1.1.isLt
    omega
  simp only [hdepth] at hweight
  apply hweight.trans_eq
  have hw := queryDependencyExpansion_weighted depth index program
    (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) (fun d => 1 + source.length ⌈/⌉ M ^ (J - d)) root
  change _ = (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
    tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).depthWeightedCount
      (fun d => 1 + source.length ⌈/⌉ M ^ (_ - d))
  rw [show (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).depth = depth root from
    queryDependencyExpansion_depth depth index program
      (chargedRandomRequestList_progress source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody) root]
  rw [hroot]
  exact hw.symm

theorem chargedRandomCoarseQuery_fresh_width_le
    (root : ChargedPhysicalRequest M J target.length passes copies T S)
    (hroot : depth root = J) :
    (∑ entry, selectionIndicator (entry ∈ (coarse root).keys (fun entry => (initial entry : ℚ))) *
      (1 + (source.length ⌈/⌉ M ^ entry.1.1.val : ℕ) : ℝ)) ≤
    ((chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork M source.length : ℝ) := by
  classical
  have hf := sum_selected_nat_weights_le ((coarse root).keys (fun entry => (initial entry : ℚ)))
    (fun entry => 1 + source.length ⌈/⌉ M ^ entry.1.1.val)
  have hw := chargedRandomCoarseQuery_width_cost_le source target N P H T S passes copies factor multiplier
    tau eta kappa delta readGroup readInteger sourceAnswer initial group integer hbody root hroot
  rw [FiniteQuery.cost_eq_sum] at hw
  have hwR : (((coarse root).keys (fun entry => (initial entry : ℚ))).map
      (fun entry => 1 + source.length ⌈/⌉ M ^ entry.1.1.val)).sum ≤
      (chargedRandomDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hbody root).widthWork M source.length := hw
  have hwcast := (Nat.cast_le (α := ℝ)).mpr hwR
  apply le_trans ?_ hwcast
  simpa only [Nat.cast_add, Nat.cast_one] using hf

end Coarse

end EditApproximation

end OAI
