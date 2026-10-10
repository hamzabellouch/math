import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.NativeSharp
import OAI.LinearAlgebra.MatrixFields.Construction.OrderedLimits

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
namespace MatrixMultiplication.AllFieldMain
open AllFieldNativeCapacity AllFieldTerminalRates AllFieldInitialEntropy NativeNumerics

universe u

theorem omega_lt_source_constant (F : Type u) [Field F] :
    Arithmetic.omega F < (2371054886006746 : ℝ) / 10 ^ 15 ∧
    (2371054886006746 : ℝ) / 10 ^ 15 < (2371056 : ℝ) / 10 ^ 6 := by
  constructor
  · have hbound := AllFieldOrderedLimits.omega_le_native_ratio F
      native_denominator_gap native_stageC_feasible
      native_stageA_positive native_stageB_positive
      native_stageC_balanced_positive native_volume_positive
    exact lt_of_le_of_lt hbound native_sharp_rate_bound
  · norm_num

end MatrixMultiplication.AllFieldMain

end

end MatrixAllFields

end OAI
