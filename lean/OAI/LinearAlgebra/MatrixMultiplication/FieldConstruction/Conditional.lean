import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.OrderedLimits

namespace OAI

/-! Tensor extraction over arbitrary fields and its asymptotic rate. -/

namespace MatrixMultiplication.AllFieldConditional

open AllFieldNativeCapacity

structure NumericalConditions : Prop where

  denominator_gap : nativeB < nativeHigh

  stageA_positive : ∀ i : Fin 3, 0 < nativeLA i

  stageB_positive : ∀ i : Fin 3, 0 < nativeLB i

  stageC_positive : ∀ i : Fin 3,
    0 < nativeCstar - (nativeLA i + nativeLB i)

  stageC_feasible : ∀ i : Fin 3,
    nativeCstar - (nativeLA i + nativeLB i) < nativeHigh

  volume_positive : 0 < AllFieldTerminalRates.S

  strict_rate_bound :
    3 * (8 * Real.log 7 -
      (AllFieldInitialEntropy.nativeH0 + nativeCstar)) / AllFieldTerminalRates.S <
        (2371054887 : ℝ) / 10 ^ 9

theorem omega_lt_2371054887_div_1000000000_of_numerical_conditions
    (F : Type*) [Field F] (h : NumericalConditions) :
    Arithmetic.omega F < (2371054887 : ℝ) / 10 ^ 9 := by
  have hc (i : Fin 3) : 0 < nativeLC nativeLambda i := by
    rw [nativeLC_balanced h.denominator_gap i]
    exact h.stageC_positive i
  have hbound := AllFieldOrderedLimits.omega_le_native_ratio F
    h.denominator_gap h.stageC_feasible
    h.stageA_positive h.stageB_positive hc h.volume_positive
  exact lt_of_le_of_lt hbound h.strict_rate_bound

end MatrixMultiplication.AllFieldConditional

end OAI
