import OAI.Combinatorics.EditApproximation.Geometry.ChargedDependencyExpansion

namespace OAI

/-! Almost-linear bounds for the executed request tree. These count
requests and depth-weighted source widths, independently of accuracy events.
Local arithmetic and random-source costs are separate obligations. -/

namespace EditApproximation

open Filter
open scoped Topology

namespace DependencyExpansion

theorem nodeCount_le_depthWeightedCount (weight : ℕ → ℕ)
    (hweight : ∀ d, 1 ≤ weight d) (tree : DependencyExpansion) :
    tree.nodeCount ≤ tree.depthWeightedCount weight := by
  induction tree with
  | node d k m n same earlier ihs ihe =>
    exact Nat.add_le_add (Nat.add_le_add (hweight d) (Finset.sum_le_sum fun i _ => ihs i))
      (Finset.sum_le_sum fun i _ => ihe i)

theorem nodeCount_le_widthWork (M n : ℕ) (tree : DependencyExpansion) :
    tree.nodeCount ≤ tree.widthWork M n :=
  nodeCount_le_depthWeightedCount _ (fun _ => by omega) tree

end DependencyExpansion

/-- The deterministic balanced-tree prefactor is only `N` times a fixed
polynomial in the logarithmic height. -/
theorem computed_width_prefactor_le (N n : ℕ) (hN : 0 < N) (hn : n ≤ N)
    (hell : 200 ≤ inputSmallLog N) (hH : 105 ≤ inputHeight N) :
    (intervalTreeDepth (integerParameters N).M n + 1) * n +
      4 * (integerParameters N).M * max 1 n ≤ (N + 2) * inputHeight N ^ 2 := by
  have hdepth := computed_tree_depth_bound N n hN hn hell
  have hellone : 1 ≤ inputSmallLog N := by omega
  have hJ : intervalTreeDepth (integerParameters N).M n ≤ 100 * inputHeight N := by
    have hm := Nat.mul_le_mul_left (intervalTreeDepth (integerParameters N).M n) hellone
    omega
  have hM : (integerParameters N).M ≤ inputHeight N := by
    change 2 ^ (heightExponent N / 20) ≤ 2 ^ heightExponent N
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  have hx : max 1 n ≤ N + 2 := max_le (by omega) (by omega)
  calc
    _ ≤ (100 * inputHeight N + 1) * (N + 2) +
        4 * inputHeight N * (N + 2) := by gcongr; omega
    _ ≤ 105 * inputHeight N * (N + 2) := by nlinarith
    _ ≤ (N + 2) * inputHeight N ^ 2 := by
      have hsquare : 105 * inputHeight N ≤ inputHeight N ^ 2 := by nlinarith
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (N + 2) hsquare

/-- Fixed height-polynomial overheads can be included in the executed
width-work estimate without changing its almost-linear exponent. -/
theorem computed_weighted_widthWork_near_linear (C : ℕ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ n ≤ N, ∀ tree : DependencyExpansion,
      tree.Valid ((integerParameters N).M * inputSmallLog N ^ 257)
        (inputHeight N ^ (512 * (coarseExponent (inputSmallLog N) + 1))) →
      tree.depth = intervalTreeDepth (integerParameters N).M n →
      tree.rank ≤ computedDependencyIndexCount N →
      (tree.widthWork (integerParameters N).M n : ℝ) * (inputHeight N : ℝ) ^ C ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := (computedDependencyOverheadExponent_tendsto 257 512).add
    (hlog.const_mul (C + 2 : ℝ))
  simp only [mul_zero, zero_add] at hlimit
  have hfinal := sublinear_height_near_linear
    (fun N => computedDependencyOverheadExponent 257 512 N +
      (C + 2 : ℝ) * Real.log (inputHeight N : ℝ)) (by
        convert hlimit using 1
        ext N
        ring) epsilon hepsilon
  filter_upwards [hfinal, eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200),
    inputHeight_real_tendsto.eventually (eventually_ge_atTop 105)] with N hfinal hN hell hH
  intro n hn tree hv hd hk
  have hHnat : 105 ≤ inputHeight N := by exact_mod_cast hH
  have hpref := computed_width_prefactor_le N n (by omega) hn hell hHnat
  have hw := DependencyExpansion.widthWork_le (integerParameters N).M n _ _ _
    (computed_branching_bounds N (by omega) hell).1 tree hv hd hk
    (Real.exp (computedDependencyOverheadExponent 257 512 N)) (Real.exp_nonneg _) (by
      intro j hj
      exact computed_dependency_path_envelope N 257 512 j
        (hj.trans (intervalTreeDepth_le_computedMax N n hn)))
  have hprefR : (((intervalTreeDepth (integerParameters N).M n + 1) * n +
      4 * (integerParameters N).M * max 1 n : ℕ) : ℝ) ≤
      (N + 2 : ℝ) * (inputHeight N : ℝ) ^ 2 := by exact_mod_cast hpref
  calc
    _ ≤ ((N + 2 : ℝ) * (inputHeight N : ℝ) ^ 2 *
        Real.exp (computedDependencyOverheadExponent 257 512 N)) *
          (inputHeight N : ℝ) ^ C := by
      exact mul_le_mul_of_nonneg_right
        (hw.trans (mul_le_mul_of_nonneg_right hprefR (Real.exp_nonneg _))) (by positivity)
    _ = (N + 2 : ℝ) * Real.exp (computedDependencyOverheadExponent 257 512 N +
        (C + 2 : ℝ) * Real.log (inputHeight N : ℝ)) := by
      rw [Real.exp_add]
      have hexp : Real.exp ((C + 2 : ℝ) * Real.log (inputHeight N : ℝ)) =
          (inputHeight N : ℝ) ^ (C + 2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using
          (nat_pow_eq_exp_log (inputHeight N) (C + 2) (by omega)).symm
      rw [hexp, pow_add]
      ring
    _ ≤ _ := hfinal

section Charged

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
local notation "depth" => @ChargedPhysicalRequest.depth M J target.length passes copies T S
local notation "index" => @ChargedPhysicalRequest.index M J target.length passes copies T S

/-- The instrumented memo evaluator makes no more requests than there
are nodes in its exact uncached expansion. -/
theorem chargedMemoEvaluate_requests_le_widthWork (hM : 1 ≤ M)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedMemoEvaluate source target N P (inputSmallLog N) (40 * smallLogExponent N)
      H (inputSmallLog N ^ 80) T S passes copies factor multiplier tau eta kappa delta
      group integer initial root).requests ≤
      (chargedDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial root).widthWork M source.length := by
  calc
    _ ≤ rankedUncachedCalls ChargedPhysicalRequest.rank program root :=
      rankedMemoEvaluate_requests_le _ _ _ _
        (ChargedPhysicalRequest.code_injective hM) (ChargedPhysicalRequest.code_fits hM)
        root .empty (memoSound_empty _ _ _)
    _ = (chargedDependencyTree source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial root).nodeCount := by
      exact (queryDependencyExpansion_nodes depth index program
        (chargedRequestList_progress source target N P H T S passes copies factor multiplier
          tau eta kappa delta group integer initial) root).symm
    _ ≤ _ := DependencyExpansion.nodeCount_le_widthWork _ _ _

theorem chargedDependencyTree_depth
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial root).depth = depth root :=
  queryDependencyExpansion_depth depth index program
    (chargedRequestList_progress source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial) root

theorem chargedDependencyTree_index_le
    (hpasses : passes = computedSeedPassCount N + 1)
    (hT : T = (integerParameters N).T) (hS : S = (integerParameters N).S)
    (root : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial root).rank ≤ computedDependencyIndexCount N := by
  rw [show (chargedDependencyTree source target N P H T S passes copies factor multiplier
      tau eta kappa delta group integer initial root).rank = index root from
    queryDependencyExpansion_index depth index program
      (chargedRequestList_progress source target N P H T S passes copies factor multiplier
        tau eta kappa delta group integer initial) root]
  have hi := chargedRequest_index_le root
  apply hi.trans_eq
  simp only [computedDependencyIndexCount, hpasses, hT, hS]

end Charged

end EditApproximation

end OAI
