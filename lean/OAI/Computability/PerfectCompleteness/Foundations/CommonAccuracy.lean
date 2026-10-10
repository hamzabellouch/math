import OAI.Computability.PerfectCompleteness.Construction.AscendingBranchingLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedRows

namespace OAI

section

namespace PerfectCompleteness.CommonAccuracy

open FixedRows InitialParameters UpperParameterScalars

noncomputable section

variable {δ : ℚ} (plan : Plan δ)

def tolerance (j : Nat) : ℝ :=
  min (epsilon δ ^ 2 / 40)
    (min (simultaneous δ ^ 2 / 160)
      (min (plan.density * q (inverse δ) plan.order (rows plan j) / 160)
        (min (gamma (useful δ) plan.density (inverse δ) plan.order (rows plan j) ^ 2 / 640)
          (gamma (useful δ) plan.density (inverse δ) plan.order (rows plan j) / 40))))

theorem tolerance_pos (hδ : 0 < δ) (j : Nat) : 0 < tolerance plan j := by
  have hε := epsilon_pos hδ
  have hc := simultaneous_pos hδ
  have hq := q_pos (inverse_pos hδ) plan.order (rows plan j)
  have hγ := gamma_pos (useful_pos hδ) plan.density_pos (inverse_pos hδ)
    plan.order (rows plan j)
  have hα := plan.density_pos
  unfold tolerance
  positivity

theorem exists_accuracy (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j ≤ plan.depth,
      ε < epsilon δ ^ 2 / 40 ∧
      ε < simultaneous δ ^ 2 / 160 ∧
      ε < plan.density * q (inverse δ) plan.order (rows plan j) / 160 ∧
      ε < gamma (useful δ) plan.density (inverse δ) plan.order (rows plan j) ^ 2 / 640 ∧
      ε < gamma (useful δ) plan.density (inverse δ) plan.order (rows plan j) / 40 := by
  obtain ⟨ε, hε, hsmall⟩ := AscendingBranching.exists_common_accuracy
    (fun j : Fin (plan.depth + 1) => tolerance plan j.val)
    (fun j => tolerance_pos plan hδ j.val)
  refine ⟨ε, hε, fun j hj => ?_⟩
  have h := hsmall ⟨j, Nat.lt_succ_of_le hj⟩
  simpa only [tolerance, lt_min_iff] using h

end
end PerfectCompleteness.CommonAccuracy

end

end OAI
