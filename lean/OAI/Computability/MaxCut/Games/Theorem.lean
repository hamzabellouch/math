import Mathlib
import OAI.Computability.MaxCut.Encoding.MatrixGap

namespace OAI

namespace MaxCutGames.Theorem

theorem exists_binaryGapReduction (ε δ : ℝ)
    (hε : 0 < ε) (_hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (_hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) := by
  obtain ⟨P⟩ := ParameterSelection.exists_outerParameters ε δ hε hδ
  obtain ⟨M⟩ := Decoder.MatrixGap.exists_parameters P.pStar P.pStar_pos
  exact ⟨FromMatrixGap.reduction P M⟩

end MaxCutGames.Theorem

namespace MaxCutGames

/-- For every fixed pair of errors in `(0, 1/2)`, binary 3SAT reduces in
polynomial time to translation Unique Games with completeness at least `1 - ε`
and soundness at most `δ`. The alphabet and machine depend only on the errors. -/
theorem theorem11 (ε δ : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Nonempty (Explicit.MachineOutputContract.BinaryGapReduction ε δ) :=
  Theorem.exists_binaryGapReduction ε δ hε hεhalf hδ hδhalf

end MaxCutGames

end OAI
