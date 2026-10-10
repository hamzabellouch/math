import OAI.Combinatorics.ContingencyTables.Counting.CountingMachineEvents

namespace OAI

/-! # The finite rational event in the main counting statement -/
namespace ContingencyTables.CountingMachineEvents
open MatchingFPRAS MatchingFPRAS.PhysicalStream CommonBasesFPRAS
open scoped Classical
noncomputable section
variable {wordCount : List Symbol→ℕ} {output : List Symbol×List Bool→List Symbol}
variable {m n : ℕ}

theorem goodTapes_success (N : TreeTyped.Realizer wordCount) (F : TreeTyped.Realizer output)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ)
    (hout : ∀ bs,∀ a∈output (Algorithms.encodeCountingInput r c b epsilon delta,bs),a≠6 ∧ a≠7)
    (draw : Bits (wordCount (Algorithms.encodeCountingInput r c b epsilon delta))→ℚ)
    (hf : ∀ bits,output (Algorithms.encodeCountingInput r c b epsilon delta,List.ofFn bits)=encodeRat (draw bits))
    (hs : 1-(delta:ℝ) ≤ uniformAverage (fun bits =>
      if (1-epsilon)*(Algorithms.count r c b:ℚ)≤draw bits ∧
        draw bits≤(1+epsilon)*(Algorithms.count r c b:ℚ) then (1:ℝ) else 0))
    (t : ℕ) (ht : FiniteWordExecution.machineTime N F
      (Algorithms.encodeCountingInput r c b epsilon delta)≤t) :
    1-delta ≤ ((Algorithms.goodCountingTapes (FiniteWordExecution.machine N F)
      r c b epsilon delta t).card:ℚ)/(2:ℚ)^t := by
  apply success N F (Algorithms.encodeCountingInput r c b epsilon delta)
    (CountingInputSymbols.counting_nonzero r c b epsilon delta) hout draw hf
    (fun q => (1-epsilon)*(Algorithms.count r c b:ℚ)≤q ∧
      q≤(1+epsilon)*(Algorithms.count r c b:ℚ)) delta ?_ t ht
  convert hs using 1
  congr 1
  funext bits
  split_ifs <;> rfl

end
end ContingencyTables.CountingMachineEvents

end OAI
