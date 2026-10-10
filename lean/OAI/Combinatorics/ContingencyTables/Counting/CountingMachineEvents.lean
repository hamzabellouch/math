import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordRationalLaw
import OAI.Combinatorics.ContingencyTables.Counting.CountingInputSymbols
import OAI.Combinatorics.ContingencyTables.Counting.CountingBranchProgram

namespace OAI

/-! # From the counting experiment's real probability bound to public tapes -/
namespace ContingencyTables.CountingMachineEvents
open MatchingFPRAS MatchingFPRAS.PhysicalStream CommonBasesFPRAS
open scoped BigOperators Classical
noncomputable section

lemma average_cast (n : ℕ) (f : Bits n→ℚ) :
    (average f:ℝ)=uniformAverage (fun bits => (f bits:ℝ)) := by
  simp only [average,uniformAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_pow,Rat.cast_ofNat,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]

variable {wordCount : List Symbol→ℕ} {output : List Symbol×List Bool→List Symbol}

theorem success (N : TreeTyped.Realizer wordCount) (F : TreeTyped.Realizer output)
    (as : List Symbol) (ha : ∀ a∈as,a≠0)
    (hout : ∀ bs,∀ a∈output (as,bs),a≠6 ∧ a≠7)
    (draw : Bits (wordCount as)→ℚ) (hf : ∀ bits,output (as,List.ofFn bits)=encodeRat (draw bits))
    (P : ℚ→Prop) (delta : ℚ)
    (hs : 1-(delta:ℝ) ≤ uniformAverage (fun bits : Bits (wordCount as) => if P (draw bits) then 1 else 0))
    (t : ℕ) (ht : FiniteWordExecution.machineTime N F as ≤ t) :
    1-delta ≤ ((Finset.univ.filter (fun bits : Bits t =>
      ∃ q : ℚ,Outputs (FiniteWordExecution.machine N F) as bits q ∧ P q)).card:ℚ)/(2:ℚ)^t := by
  have hm := FiniteWordExecution.machine_rational_event N F as ha hout draw hf P t ht
  apply le_trans ?_ hm
  have hc : ((1-delta:ℚ):ℝ) ≤
      ((average (fun bits : Bits (wordCount as) => if P (draw bits) then (1:ℚ) else 0)):ℝ) := by
    rw [average_cast]
    simpa only [Rat.cast_sub,Rat.cast_one,apply_ite,Rat.cast_zero] using hs
  exact_mod_cast hc

end
end ContingencyTables.CountingMachineEvents

end OAI
