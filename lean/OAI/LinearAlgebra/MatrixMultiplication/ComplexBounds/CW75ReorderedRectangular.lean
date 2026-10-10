import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedBalancedRates
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.CurveRationalLaw

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

namespace MatrixMultiplication.CW75ReorderedRectangular

open MatrixMultiplication.Foundation ConditionalLabels ComplexWitness
open CW75ReorderedBalanced CW75ReorderedBalancedRates
open scoped BigOperators

theorem rectangularOmega_lt_target :
    Arithmetic.rectangularOmega ℂ ((709 : ℝ) / 1000) < (523 : ℝ) / 250 := by
  obtain ⟨counts, hD, h_lower, h_upper, g_lower, _g_upper⟩ :=
    CurveLaws.exists_count_rate_bounds
  let p := normalizedCountLaw counts hD
  have mass : ∀ a, p.mass a = (counts a : ℝ) / (∑ b, counts b : ℕ) := fun _ => rfl
  exact RectangularWitness.omega_lt_target_of_nearby_balanced_family
    (witness counts) (fun t => (t : ℝ) * (∑ a, counts a : ℕ))
    (lawPairingRate p curveLabels 5 curveReaderPair .yz)
    (lawPairingRate p curveLabels 5 curveReaderPair .xy +
      lawPairingRate p curveLabels 5 curveReaderPair .xz)
    (finiteEntropy p.mass) g_lower h_lower h_upper
    (scale_eventually_pos counts hD)
    (tendsto_log_witness_outer counts hD p mass)
    (tendsto_log_witness_inner counts hD p mass)
    (tendsto_log_witness_multiplicity counts hD p mass)
    (tendsto_log_witness_rank counts hD p mass)

end MatrixMultiplication.CW75ReorderedRectangular

end OAI
