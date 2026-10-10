import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalRefinement
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalGroupProgram

namespace OAI

/-! On good seeds, the query-local recurrence equals the complete refinement recurrence. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q H T : ℕ) (A tau delta eta kappa : ℚ)
  (online : PhysicalOnlineStreams source target U N P F A T exponent H tau R)
  (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)

local notation "provider" => physicalProgramOnline source target U N P F A T exponent H tau eta kappa online
local notation "choices" => physicalProgramSelections source target U N P F A T exponent H Q tau eta kappa online
  (physicalGroupStreamsOfKeys source target U N P F exponent Q A draw)
local notation "localDraw" => (fun node t => draw node (Fin.ofNat R (t - 1)))

theorem physicalLocalRefinement_keyed_eq
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T localDraw provider node t q =
      physicalRefinement source target U N P F A T delta choices node t q := by
  rw [physicalLocalRefinement, physicalRefinement]
  split_ifs with hbelow hleaf
  · rfl
  · have hchild (i : Fin M) : physicalLocalRefinement source target U N P F exponent Q A tau delta T
        localDraw provider (physicalChild node hbelow i) =
        physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i) := by
      funext s r
      exact physicalLocalRefinement_keyed_eq hsize hP hF hA hseed (physicalChild node hbelow i) s r
    dsimp only
    simp_rw [hchild]
    cases t with
    | zero => exact physicalLocalWarmup_eq source target U N P F A hsize hP hF hA hseed T (node, q)
    | succ t =>
      let children : PhysicalChildTables M target.length := fun i =>
        physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
      have hmass : physicalLocalChildMass source target U N P F A T node hbelow =
          physicalBandChildMassTable source target U N P F A T node hbelow := by
        funext i r
        exact physicalLocalWarmupMass_eq source target U N P F A hsize hP hF hA hseed T
          (physicalChild node hbelow i, r)
      have hfactor := refinementFactor_spec A F (by omega : 0 < F)
      have hspatial : ∀ r, |stageInitial source target U N P F A (node, q) -
          stageInitial source target U N P F A (node, r)| ≤ 32 * F * targetEndpointDistance q r := by
        intro r
        have hqr := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
          hsize hP hF hA hfactor.1 hfactor.2 hseed node q r
        have hrq := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
          hsize hP hF hA hfactor.1 hfactor.2 hseed node r q
        have hsym : targetEndpointDistance r q = targetEndpointDistance q r := by
          exact congrArg₂ (· + ·) (Nat.dist_comm _ _) (Nat.dist_comm _ _)
        rw [hsym] at hrq
        apply abs_le.mpr
        constructor <;> dsimp only [stageInitial] <;> linarith only [hqr, hrq]
      have hold (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i t r :=
        physicalRefinement_nonneg_all_seeds source target U N P F A T delta choices
          (physicalChild node hbelow i) t r
      have hcurrent (i : Fin M) (r : TargetInterval target.length) : 0 ≤ children i (t + 1) r :=
        physicalRefinement_nonneg_all_seeds source target U N P F A T delta choices
          (physicalChild node hbelow i) (t + 1) r
      have hstep := rationalLocalWideStep_eq source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F) delta
        (fun r => stageInitial source target U N P F A (node, r))
        (physicalLocalChildMass source target U N P F A T node hbelow)
        (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
        (fun i r => children i t r) (fun i r => children i (t + 1) r)
        (draw ⟨node, hbelow⟩ (Fin.ofNat R t)) (provider node children (t + 1) q) q
        hfactor.1 hF (stageInitial_nonneg_all_seeds source target U N P F A (node, q)) hold hcurrent hspatial
      rw [hmass] at hstep
      have hkey := physicalProgramGroups_keyed source target U N P F exponent Q A T tau draw node hbelow children (t + 1)
      simp only [Nat.add_sub_cancel] at hkey
      unfold physicalBandChildInitial at hkey
      rw [← hkey] at hstep
      change rationalLocalWideStep source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F) delta
        (fun r => stageInitial source target U N P F A (node, r))
        (physicalLocalChildMass source target U N P F A T node hbelow)
        (fun i r => stageInitial source target U N P F A (physicalChild node hbelow i, r))
        (fun i r => children i t r) (fun i r => children i (t + 1) r)
        (draw ⟨node, hbelow⟩ (Fin.ofNat R t)) (provider node children (t + 1) q) q = _
      rw [hmass]
      exact hstep
  · rfl
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

end Program

end EditApproximation

end OAI
