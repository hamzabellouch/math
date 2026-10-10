import OAI.Analysis.KadisonKastler.RegularActionPackets
import OAI.Analysis.KadisonKastler.L2TensorCoordinates

namespace OAI

/-! # Agreement of the two concrete elementary-tensor constructions -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularTensorVector_eq_scalarLpTensor
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    regularTensorVector f v = scalarLpTensor volume f v := by
  apply Lp.ext
  filter_upwards [regularTensorVector_apply_ae f v,
    scalarLpTensor_apply_ae volume f v] with t ht hs
  exact ht.trans hs.symm

theorem regularFrequencyPacket_eq_scalarLpTensor
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    regularFrequencyPacket f v =
      scalarLpTensor volume ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f) v :=
  (regularFrequencyPacket_eq_tensor f v).trans (regularTensorVector_eq_scalarLpTensor _ v)

end

end KadisonKastler

end OAI
