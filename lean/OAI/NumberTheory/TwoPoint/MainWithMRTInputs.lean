import OAI.NumberTheory.TwoPoint.PartiallyDischargedMain
import OAI.NumberTheory.TwoPoint.Circuits.BravermanDepth22Theorem

namespace OAI

/-! The three manuscript main results after discharging both prime inputs
and the fixed-depth Braverman input. Only the published MRT inputs remain. -/

namespace TwoPointCorrelations

theorem liouvilleLogSaving_of_mrt (hMRT : MRTLiouvilleShortInput) : LiouvilleLogSaving :=
  liouvilleLogSaving_of_circuit_mrt bravermanDepth22Input hMRT

theorem binaryCorrectedElliott_of_mrt (hMRT : MRTShortExponentialInput) : BinaryCorrectedElliott :=
  binaryCorrectedElliott_of_circuit_mrt bravermanDepth22Input hMRT

theorem affineCorrectedElliott_of_mrt (hMRT : MRTShortExponentialInput) : AffineCorrectedElliott :=
  affineCorrectedElliott_of_circuit_mrt bravermanDepth22Input hMRT

end TwoPointCorrelations

end OAI
