import OAI.Algebra.DepthFive.Basic
import OAI.Algebra.DepthFive.UpperConstruction
import OAI.Algebra.DepthFive.UpperBoundArithmetic
import OAI.Algebra.DepthFive.CharacteristicZeroTransfer
import OAI.Algebra.DepthFive.ConfiguredImmSecondMoment
import OAI.Algebra.DepthFive.LowerBoundAssembly

namespace OAI

noncomputable section

universe u

namespace Problem335

theorem complex_depth_five_lower_bound :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit ℂ n, circuitValue c = imm ℂ n → (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  exact complex_depth_five_lower_bound_of_eventual_second_trace 10
    LowerParameters.eventually_configured_imm_second_moment_upper

theorem characteristic_zero_depth_five_lower_bound :
    ∃ n0 : ℕ, ∀ (K : Type u) [Field K] [CharZero K], ∀ n : ℕ, n0 ≤ n → ∀ c : Depth5Circuit K n, circuitValue c = imm K n → (n : ℝ) ^ (Real.sqrt (n : ℝ) / 400) ≤ (circuitSize c : ℝ) := by
  exact characteristic_zero_depth_five_lower_bound_of_complex complex_depth_five_lower_bound

theorem all_field_depth_five_upper_bound :
    ∀ (K : Type u) [Field K] (n : ℕ), 2 ≤ n → ∃ c : Depth5Circuit K n, circuitValue c = imm K n ∧ circuitSize c ≤ upperGateBound n ∧ (upperGateBound n : ℝ) ≤ (n : ℝ) ^ (Real.sqrt (n : ℝ) + 4) := by
  intro K _ n hn
  obtain ⟨c, hc, hs⟩ := exists_imm_circuit_le_upperGateBound K n hn
  exact ⟨c, hc, hs, upperGateBound_le_rpow n hn⟩

theorem main :
    (∃ threshold : ℕ, ∀ size : ℕ, threshold ≤ size →
      ∀ circuit : Depth5Circuit ℂ size, circuitValue circuit = imm ℂ size →
        (size : ℝ) ^ (Real.sqrt (size : ℝ) / 400) ≤ (circuitSize circuit : ℝ)) ∧
    (∃ threshold : ℕ, ∀ (FieldType : Type u) [Field FieldType] [CharZero FieldType],
      ∀ size : ℕ, threshold ≤ size → ∀ circuit : Depth5Circuit FieldType size,
        circuitValue circuit = imm FieldType size →
          (size : ℝ) ^ (Real.sqrt (size : ℝ) / 400) ≤ (circuitSize circuit : ℝ)) ∧
    (∀ (FieldType : Type u) [Field FieldType] (size : ℕ), 2 ≤ size →
      ∃ circuit : Depth5Circuit FieldType size, circuitValue circuit = imm FieldType size ∧
        circuitSize circuit ≤ upperGateBound size ∧
        (upperGateBound size : ℝ) ≤ (size : ℝ) ^ (Real.sqrt (size : ℝ) + 4)) := by
  exact ⟨complex_depth_five_lower_bound,
    characteristic_zero_depth_five_lower_bound, all_field_depth_five_upper_bound⟩

end Problem335

end

end OAI
