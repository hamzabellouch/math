import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedFinite

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedFiniteRates

open MatrixMultiplication.Foundation CW75LabelHierarchy StageHierarchyResources
open CW75ReorderedFinite ComplexWitness Filter
open scoped BigOperators Topology Classical

theorem tendsto_log_copies (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a)
    (p : FiniteLaw Scalar)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ)) :
    Tendsto (fun t : ℕ => Real.log (copies counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy p.mass)) := by
  have hmass : (fun a => (counts a : ℝ) / (∑ b, counts b : ℕ)) = p.mass :=
    (funext mass).symm
  simpa only [copies, hmass] using tendsto_log_exactWords_card_mul counts hD

theorem tendsto_log_auxiliaryBudget (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a)
    (p : FiniteLaw Scalar)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ)) :
    Tendsto (fun t : ℕ => Real.log (stageAuxiliaryBudget counts curveLabels 5 t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (finiteEntropy p.mass)) := by
  have hmass : (fun a => (counts a : ℝ) / (∑ b, counts b : ℕ)) = p.mass :=
    (funext mass).symm
  simpa only [hmass] using tendsto_log_stageAuxiliaryBudget counts hD curveLabels 5
    curve_completeRecord_injective

theorem tendsto_log_sourceRank (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a) :
    Tendsto (fun t : ℕ => Real.log ((27 ^ blocks counts t : ℕ) : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (3 * Real.log 3)) := by
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hD' : ((∑ a, counts a : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
  have htD : (t : ℝ) * (∑ a, counts a : ℕ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr ht) hD'
  rw [Nat.cast_pow, Real.log_pow, blocks, Nat.cast_mul]
  change 3 * Real.log 3 =
    ((t : ℝ) * (∑ a, counts a : ℕ)) * Real.log 27 /
      ((t : ℝ) * (∑ a, counts a : ℕ))
  rw [mul_div_cancel_left₀ _ htD, hlog27]

theorem tendsto_log_rankBudget (counts : Scalar → ℕ) (hD : 0 < ∑ a, counts a)
    (p : FiniteLaw Scalar)
    (mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ)) :
    Tendsto (fun t : ℕ => Real.log (rankBudget counts t : ℝ) /
      ((t : ℝ) * (∑ a, counts a : ℕ))) atTop
      (𝓝 (3 * Real.log 3 + finiteEntropy p.mass)) := by
  apply ((tendsto_log_sourceRank counts hD).add
    (tendsto_log_auxiliaryBudget counts hD p mass)).congr
  intro t
  have hsource : ((27 ^ blocks counts t : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hauxiliary : (stageAuxiliaryBudget counts curveLabels 5 t : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.ne_of_gt (stageAuxiliaryBudget_pos counts curveLabels 5 t))
  rw [rankBudget, Nat.cast_mul, Real.log_mul hsource hauxiliary, add_div]

end MatrixMultiplication.CW75ReorderedFiniteRates

end

end OAI
