import OAI.Combinatorics.EditApproximation.Binary.BinaryActionSelection
import OAI.Combinatorics.EditApproximation.Binary.BinaryOptimizerSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction

theorem scoredArgmaxWithWork_count {α : Type*} (score : α → BinaryFraction × ℕ) (values : List α) :
    values.length ≤ (scoredArgmaxWithWork score values).2 := by
  induction values with
  | nil => exact Nat.zero_le _
  | cons value rest ih =>
    simp only [scoredArgmaxWithWork, List.length_cons]
    split <;> dsimp only <;> omega

/-- Includes the pointer list passed to the optimizer, then the final
label-preserving gradient and maximum scan. -/


theorem selectionAllocation_le_work {α : Type*} {d : ℕ}
    (vertices : List (α × Vector BinaryFraction d)) (linear : Vector BinaryFraction d) (G j : ℕ) :
    selectionAllocation vertices linear G j ≤ 2 * (selectionWithWork vertices linear G j).2 := by
  let iterate := (finiteOptimizerWithWork (vertices.map Prod.snd) linear G j).1
  let gradient := (gradientWithWork G linear iterate).1
  have hi := optimizerAllocation_le_work (vertices.map Prod.snd) linear G j
  have hg := gradientAllocation_le_work G linear iterate
  have hs := scoredArgmaxAllocation_le_work (fun vertex : α × Vector BinaryFraction d =>
    dotWithWork gradient vertex.2) (fun vertex => dotListAllocation gradient vertex.2 (List.finRange d)) vertices
    (fun vertex _ => dotListAllocation_le_work gradient vertex.2 (List.finRange d))
  have hn := scoredArgmaxWithWork_count (fun vertex : α × Vector BinaryFraction d => dotWithWork gradient vertex.2) vertices
  unfold selectionAllocation selectionWithWork
  dsimp only [iterate, gradient] at hi hg hs hn ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
