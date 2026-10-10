import OAI.Combinatorics.EditApproximation.Geometry.LocalWideStep
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalWarmup

namespace OAI

/-! The local finite refinement recurrence, with direct query groups and
local warmup data. Current-index dependencies go only to physical children;
the recurrence is well founded before any accuracy assertion. -/

namespace EditApproximation

def physicalLocalChildMass {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (T : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J) :
    Fin M → TargetInterval target.length → ℚ :=
  fun i r => physicalLocalWarmupMass source target U N P F A T (physicalChild node hbelow i, r)

def physicalLocalRefinement {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (node : PhysicalNode M J) : ℕ → TargetInterval target.length → ℚ :=
  if hbelow : node.1.val < J then
    if (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo ≤ 1 then
      fun _ q => stageInitial source target U N P F A (node, q)
    else
      let children : PhysicalChildTables M target.length := fun i =>
        physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online
          (physicalChild node hbelow i)
      fun t q => match t with
        | 0 => physicalLocalWarmup source target U N P F A T (node, q)
        | s + 1 => rationalLocalWideStep source target (physicalSourceInterval source.length node)
            N P F exponent Q tau (refinementFactor A F) delta
            (fun r => stageInitial source target U N P F A (node, r))
            (physicalLocalChildMass source target U N P F A T node hbelow)
            (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
            (fun i r => children i s r) (fun i r => children i (s + 1) r)
            (draw ⟨node, hbelow⟩ (s + 1)) (online node children (s + 1) q) q
  else fun _ q => stageInitial source target U N P F A (node, q)
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

theorem physicalLocalRefinement_bounds {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ) (hdelta : 0 ≤ delta)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (online : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    0 ≤ physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node t q ∧
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online node t q ≤
        stageInitial source target U N P F A (node, q) := by
  rw [physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A (node, q), le_rfl⟩
  · cases t with
    | zero => exact physicalLocalWarmup_bounds source target U N P F A T (node, q)
    | succ t =>
      let children : PhysicalChildTables M target.length := fun i =>
        physicalLocalRefinement source target U N P F exponent Q A tau delta T draw online
          (physicalChild node hbelow i)
      have hold (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i t r :=
        (physicalLocalRefinement_bounds source target U N P F exponent Q A tau delta T hdelta
          draw online (physicalChild node hbelow i) t r).1
      have hcurrent (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i (t + 1) r :=
        (physicalLocalRefinement_bounds source target U N P F exponent Q A tau delta T hdelta
          draw online (physicalChild node hbelow i) (t + 1) r).1
      exact rationalLocalWideStep_bounds source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F) delta
        (fun r => stageInitial source target U N P F A (node, r))
        (physicalLocalChildMass source target U N P F A T node hbelow)
        (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
        (fun i r => children i t r) (fun i r => children i (t + 1) r)
        (draw ⟨node, hbelow⟩ (t + 1)) (online node children (t + 1) q) q hdelta
        (stageInitial_nonneg_all_seeds source target U N P F A (node, q)) hold hcurrent
  · exact ⟨stageInitial_nonneg_all_seeds source target U N P F A (node, q), le_rfl⟩
termination_by J - node.1.val
decreasing_by
  all_goals
    unfold physicalChild
    dsimp only
    omega

end EditApproximation

end OAI
