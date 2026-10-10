import Mathlib
import OAI.Probability.BinarySweep.Model
import OAI.Probability.BinarySweep.Conditional.ConditionalSign
import OAI.Probability.BinarySweep.Mixing.BinaryMixingBounds

namespace OAI

open scoped BigOperators

theorem binary_sweep_contraction_and_mixing :
    BinaryCoordinateSweeps.BinaryContractionTarget ∧
    (∀ d : ℕ, 0 < d → ∑ g : Equiv.Perm (BinaryCoordinateSweeps.Slot d),
      BinaryCoordinateSweeps.binaryLaw d g * BinaryCoordinateSweeps.realSign g = 0) ∧
    BinaryCoordinateSweeps.UniformSweepMixingTarget :=
  BinaryCoordinateSweeps.binary_main

end OAI
