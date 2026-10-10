import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ConstructionLabels
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RecoveryBudget
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.SourceRates

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

noncomputable section

namespace MatrixMultiplication.AllFieldConstructionRates

open MatrixMultiplication.Foundation AllFieldHistory Filter
open scoped BigOperators Topology Classical

variable {K : ℕ}

abbrev Copies (allocation : Allocation) (ε : ℝ) (m : ℕ) :=
  ∀ tick : Fin (K + 2), InverseLinearRecovery.MaskRectangles
    (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick.val) allocation ε m)

theorem card_copies (allocation : Allocation) (ε : ℝ) (m : ℕ) :
    Fintype.card (Copies (K := K) allocation ε m) =
      ∏ tick : Fin (K + 2), RecoveryGrowth.replicationCount
        (AllFieldHistorySupport.supportRate (K := K) (tick := tick.val) allocation)
        (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick.val) allocation ε + 6) m := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro tick _
  exact InverseLinearRecovery.card_recovery_copies
    (AllFieldHistorySupport.supportRate (K := K) (tick := tick.val) allocation)
    (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick.val) allocation ε + 6) m

theorem card_copies_range (allocation : Allocation) (ε : ℝ) (m : ℕ) :
    Fintype.card (Copies (K := K) allocation ε m) =
      ∏ tick ∈ Finset.range (K + 2), Fintype.card
        (InverseLinearRecovery.MaskRectangles
          (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m)) := by
  rw [Fintype.card_pi]
  exact Fin.prod_univ_eq_prod_range (fun tick : ℕ => Fintype.card
    (InverseLinearRecovery.MaskRectangles
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick) allocation ε m))) (K + 2)

theorem card_copies_pos (allocation : Allocation) (ε : ℝ) (m : ℕ) :
    0 < Fintype.card (Copies (K := K) allocation ε m) := Fintype.card_pos

theorem copies_subexponential (allocation : Allocation) (ε : ℝ) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (Copies (K := K) allocation ε m) : ℝ) /
      (m : ℝ)) atTop (𝓝 0) := by
  have h := RecoveryGrowth.tendsto_log_prod_div_nat (Finset.univ : Finset (Fin (K + 2)))
    (r := fun tick m => Fintype.card (InverseLinearRecovery.MaskRectangles
      (AllFieldHistoryRecovery.shiftCount (K := K) (tick := tick.val) allocation ε m)))
    (fun _ _ _ => Fintype.card_pos)
    (fun tick _ => AllFieldHistoryRecovery.replication_subexponential
      (K := K) (tick := tick.val) allocation ε)
  simpa only [Copies, Fintype.card_pi] using h

theorem copies_rate (hK : 0 < K) (allocation : Allocation) (ε : ℝ) :
    Tendsto (fun m : ℕ => Real.log (Fintype.card (Copies (K := K) allocation ε m) : ℝ) /
      ((K : ℝ) * populationLength (K := K) allocation m)) atTop (𝓝 0) := by
  have hden : (K : ℝ) * denominator (K := K) allocation ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hK.ne')
      (Nat.cast_ne_zero.mpr (denominator_pos allocation).ne')
  have h := (copies_subexponential (K := K) allocation ε).div tendsto_const_nhds hden
  simp only [zero_div] at h
  apply h.congr
  intro m
  rw [Pi.div_apply, population_length, Nat.cast_mul]
  ring

theorem source_rank_rate (hK : 0 < K) (allocation : Allocation) (ε : ℝ) :
    Tendsto (fun m : ℕ => Real.log
      (AllFieldSource.rankBudget (Copies (K := K) allocation ε m) K
        (populationLength (K := K) allocation m) : ℝ) /
      ((K : ℝ) * populationLength (K := K) allocation m))
      atTop (𝓝 (8 * Real.log 7)) := by
  have hp := (AllFieldSourceRates.tendsto_log_polynomial_overhead K hK).comp
    (populationLength_tendsto (K := K) allocation)
  have he := (AllFieldSourceRates.tendsto_log_exponential_source K hK).comp
    (populationLength_tendsto (K := K) allocation)
  have h := ((copies_rate hK allocation ε).add hp).add he
  simp only [zero_add] at h
  apply h.congr
  intro m
  rw [AllFieldSourceRates.log_rankBudget _ _ _ (card_copies_pos allocation ε m),
    add_div, add_div]
  rfl

theorem source_rank_terminal_rate (hK : 0 < K) (allocation : Allocation) (ε : ℝ) :
    Tendsto (fun m : ℕ => Real.log
      (AllFieldSource.rankBudget
        (Copies (K := K) allocation ε (AllFieldTerminalRates.terminalDilation K m)) K
        (AllFieldTerminalRates.terminalLength allocation K m) : ℝ) /
      ((K : ℝ) * AllFieldTerminalRates.terminalLength allocation K m))
      atTop (𝓝 (8 * Real.log 7)) :=
  (source_rank_rate hK allocation ε).comp (terminalDilation_tendsto K)

theorem source_rank_terminal_rate_of_cardinality
    (ActualCopies : ℕ → Type*) [∀ m, Fintype (ActualCopies m)]
    (hK : 0 < K) (allocation : Allocation) (ε : ℝ)
    (cards : ∀ᶠ m : ℕ in atTop, Fintype.card (ActualCopies m) = Fintype.card
      (Copies (K := K) allocation ε (AllFieldTerminalRates.terminalDilation K m))) :
    Tendsto (fun m : ℕ => Real.log (AllFieldSource.rankBudget (ActualCopies m) K
      (AllFieldTerminalRates.terminalLength allocation K m) : ℝ) /
      ((K : ℝ) * AllFieldTerminalRates.terminalLength allocation K m))
      atTop (𝓝 (8 * Real.log 7)) := by
  apply (source_rank_terminal_rate hK allocation ε).congr'
  filter_upwards [cards] with m hm
  simp only [AllFieldSource.rankBudget, hm]

end MatrixMultiplication.AllFieldConstructionRates

end

end OAI
