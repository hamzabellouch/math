import OAI.LinearAlgebra.MatrixMultiplication.Entropy.CurveLaws
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexCertificates

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

noncomputable section

namespace MatrixMultiplication.CurveLaws

open ComplexWitness

theorem rpow_four (t : ℝ) : (4 : ℝ) ^ t = ((2 : ℝ) ^ t) ^ 2 := by
  rw [show (4 : ℝ) = 2 * 2 by norm_num,
    Real.mul_rpow (by norm_num) (by norm_num), pow_two]

theorem log_four : Real.log (4 : ℝ) = 2 * Real.log 2 := by
  calc
    Real.log (4 : ℝ) = Real.log ((2 : ℝ) * 2) := by norm_num
    _ = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
    _ = 2 * Real.log 2 := by ring

theorem partition_two_thirds : partition (2 / 3 : ℝ) = ComplexCertificates.curveZ := by
  rw [partition_closed, rpow_four]
  rfl

theorem hidden_two_thirds : hidden (2 / 3 : ℝ) = ComplexCertificates.curveG := by
  rw [hidden_closed, partition_two_thirds, rpow_four, log_four]
  unfold ComplexCertificates.curveG ComplexCertificates.curveU ComplexCertificates.curveV
  ring

theorem incident_two_thirds : incident (2 / 3 : ℝ) = ComplexCertificates.curveH := by
  rw [incident, partition_two_thirds, hidden_two_thirds]
  rfl

theorem incident_rate_two_thirds :
    ConditionalLabels.lawPairingRate (leafLaw (2 / 3 : ℝ))
        curveLabels 5 curveReaderPair .xy +
      ConditionalLabels.lawPairingRate (leafLaw (2 / 3 : ℝ))
        curveLabels 5 curveReaderPair .xz = ComplexCertificates.curveH := by
  rw [incident_rate, incident_two_thirds]

theorem hidden_rate_two_thirds :
    ConditionalLabels.lawPairingRate (leafLaw (2 / 3 : ℝ))
      curveLabels 5 curveReaderPair .yz = ComplexCertificates.curveG := by
  rw [hidden_rate, hidden_two_thirds]

theorem partition_two_thirds_bounds :
    (246439 : ℝ) / 5000 < partition (2 / 3 : ℝ) ∧
      partition (2 / 3 : ℝ) < (49289 : ℝ) / 1000 := by
  rw [partition_two_thirds]
  exact ComplexCertificates.curveZ_bounds

theorem hidden_two_thirds_bounds :
    (27961 : ℝ) / 25000 < hidden (2 / 3 : ℝ) ∧
      hidden (2 / 3 : ℝ) < (6991 : ℝ) / 6250 := by
  rw [hidden_two_thirds]
  exact ComplexCertificates.curveG_bounds

theorem incident_two_thirds_bounds :
    (31519 : ℝ) / 10000 < incident (2 / 3 : ℝ) ∧
      incident (2 / 3 : ℝ) < (15761 : ℝ) / 5000 := by
  rw [incident_two_thirds]
  exact ComplexCertificates.curveH_bounds

end MatrixMultiplication.CurveLaws

end

end OAI
