import OAI.Computability.PerfectCompleteness.Machines.BinaryParsingLemmas
import OAI.Computability.PerfectCompleteness.Machines.EncodingLemmas
import OAI.Computability.PerfectCompleteness.Model
import OAI.Computability.PerfectCompleteness.Reduction.Value
import OAI.Computability.UniqueGames.Machines.MachineFiniteAlphabet

namespace OAI

section

namespace PerfectCompleteness

open Turing UniqueGamesTheorem.Foundations.Complexity

namespace BinaryGapReduction

variable {δ : ℚ} (reduction : BinaryGapReduction δ)

theorem nonempty (input : List Bool) : (reduction.construct input).edges ≠ [] :=
  (reduction.construct input).nonempty

theorem exactly_two (input : List Bool)
    (edge : Fin (reduction.construct input).edges.length) (label : Fin reduction.alphabet) :
    ((List.finRange (2 * reduction.alphabet)).filter
      (fun a => decide ((reduction.construct input).edges[edge].projection.images[a] = label))).length = 2 :=
  (reduction.construct input).edges[edge].projection.exactlyTwo label

theorem malformed_soundness (input : List Bool)
    (malformed : BinaryEncoding.decodeFormula input = none) :
    (reduction.construct input).value ≤ (δ : ℝ) := by
  apply reduction.soundness input
  rintro ⟨formula, decoded, _⟩
  rw [malformed] at decoded
  cases decoded

end BinaryGapReduction
end PerfectCompleteness

end

end OAI
