import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalOnlineEquality
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalLocalRefinementEquality

namespace OAI

/-! The complete refinement is reproduced, on good incoming seeds, by
bounded cell and rounded-center loops with local warmup data throughout. -/

namespace EditApproximation

theorem physicalLocalRefinement_online_mem_congr {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F exponent Q : ℕ) (A tau delta : ℚ) (T : ℕ)
    (draw : PhysicalInternalNode M J → ℕ → CellGroupDraws M F Q)
    (left right : PhysicalNode M J → PhysicalChildTables M target.length → ℕ →
      TargetInterval target.length → List (PhysicalRationalAction M target.length))
    (hmem : ∀ node children t q action,
      action ∈ left node children t q ↔ action ∈ right node children t q)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T draw left node t q =
      physicalLocalRefinement source target U N P F exponent Q A tau delta T draw right node t q := by
  rw [physicalLocalRefinement, physicalLocalRefinement]
  split_ifs with hbelow hleaf
  · rfl
  · have hchild (i : Fin M) : physicalLocalRefinement source target U N P F exponent Q A tau delta T
        draw left (physicalChild node hbelow i) =
        physicalLocalRefinement source target U N P F exponent Q A tau delta T
          draw right (physicalChild node hbelow i) := by
      funext s r
      exact physicalLocalRefinement_online_mem_congr source target U N P F exponent Q A tau delta T
        draw left right hmem (physicalChild node hbelow i) s r
    dsimp only
    simp_rw [hchild]
    cases t with
    | zero => rfl
    | succ t =>
      unfold rationalLocalWideStep
      dsimp only
      apply rationalRefinementUpdate_online_mem_ext
      exact hmem _ _ _ _
  · rfl
termination_by J - node.1.val
decreasing_by
  unfold physicalChild
  dsimp only
  omega

section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q H T : ℕ) (A tau delta eta kappa : ℚ)
  (online : PhysicalOnlineStreams source target U N P F A T exponent H tau R)
  (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)

local notation "localDraw" => (fun node t => draw node (Fin.ofNat R (t - 1)))
local notation "localProvider" => physicalLocalOnline source target U N P F exponent H T A tau eta kappa
  (physicalOnlineIntegersOfStreams source target U N P F exponent H T A tau online)
local notation "provider" => physicalProgramOnline source target U N P F A T exponent H tau eta kappa online
local notation "choices" => physicalProgramSelections source target U N P F A T exponent H Q tau eta kappa online
  (physicalGroupStreamsOfKeys source target U N P F exponent Q A draw)

theorem physicalLocalProgram_eq
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (t : ℕ) (q : TargetInterval target.length) :
    physicalLocalRefinement source target U N P F exponent Q A tau delta T localDraw localProvider node t q =
      physicalRefinement source target U N P F A T delta choices node t q := by
  have hmem : ∀ label children s r action,
      action ∈ localProvider label children s r ↔ action ∈ provider label children s r := by
    intro label children s r action
    by_cases hbelow : label.1.val < J
    · exact physicalLocalOnline_mem_iff source target U N P F exponent H T A tau eta kappa online
        hsize hP hF hA hseed ⟨label, hbelow⟩ children s r action
    · simp only [physicalLocalOnline, physicalProgramOnline, dite_eq_right hbelow, List.not_mem_nil]
  rw [physicalLocalRefinement_online_mem_congr source target U N P F exponent Q A tau delta T
    localDraw localProvider provider hmem node t q]
  exact physicalLocalRefinement_keyed_eq source target U N P F exponent Q H T A tau delta eta kappa
    online draw hsize hP hF hA hseed node t q

end Program

end EditApproximation

end OAI
