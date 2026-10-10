import OAI.Combinatorics.EditApproximation.Refinement.StageWarmup

namespace OAI

/-! Exact source leaves remain exact throughout the actual physical warmup. -/

namespace EditApproximation

open Finset

theorem physicalSource_length_eq {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length =
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo := by
  simp only [physicalSource, substring, List.length_drop, List.length_take,
    Nat.min_eq_left (physicalSourceInterval source.length node).valid]

theorem physicalBellman_at_leaf {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℝ) (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (q : TargetInterval target.length) :
    physicalBellman source target P L initial representatives value (node, q) = initial (node, q) := by
  classical
  unfold physicalBellman
  dsimp only
  split_ifs <;> rfl

theorem physicalWarmup_at_leaf {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (t : ℕ) (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (q : TargetInterval target.length) :
    physicalWarmup source target P L initial representatives t (node, q) = initial (node, q) := by
  cases t with
  | zero => rfl
  | succ t => exact physicalBellman_at_leaf source target P L initial representatives _ node hleaf q

theorem rationalPhysicalWarmup_at_leaf {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℚ) (initial : PhysicalEntry M J target.length → ℚ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (t : ℕ) (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (q : TargetInterval target.length) :
    rationalPhysicalWarmup source target P L initial representatives t (node, q) = initial (node, q) := by
  apply (Rat.cast_inj (α := ℝ)).mp
  rw [rationalPhysicalWarmup_cast]
  exact physicalWarmup_at_leaf source target P (L : ℝ) (fun s => (initial s : ℝ)) representatives t node hleaf q

theorem stageWarmup_at_leaf {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (t : ℕ) (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (q : TargetInterval target.length) :
    stageWarmup source target U N P F A t (node, q) =
      stateEditCost (physicalSource source node) target q := by
  unfold stageWarmup
  rw [rationalPhysicalWarmup_at_leaf source target P (128 * F) _ _ t node hleaf q]
  have hlength : (physicalSource source node).length ≤ 1 := (physicalSource_length_eq source node).trans_le hleaf
  simp only [stageInitial, physicalInitialTable, ite_eq_left hlength]
  rw [shortSourceCost_eq_edit _ _ hlength]
  rfl

theorem stageWarmupMass_at_leaf {α : Type*} [DecidableEq α] {M J : ℕ} (source target : List α)
    (U : PhysicalEntry M J target.length → ℕ) (N P F : ℕ) (A : ℚ)
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J)
    (hleaf : (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1) (q : TargetInterval target.length) :
    stageWarmupMass source target U N P F A T (node, q) =
      stateEditCost (physicalSource source node) target q := by
  change (∑ t ∈ range T, stageWarmup source target U N P F A t (node, q)) / T = _
  simp_rw [stageWarmup_at_leaf source target U N P F A _ node hleaf q]
  simp only [sum_const, card_range, nsmul_eq_mul]
  have hTr : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
  exact mul_div_cancel_left₀ _ hTr

end EditApproximation

end OAI
