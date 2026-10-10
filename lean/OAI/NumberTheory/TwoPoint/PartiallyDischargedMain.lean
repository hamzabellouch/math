import OAI.NumberTheory.TwoPoint.ConditionalMain
import OAI.NumberTheory.TwoPoint.Bounds.PrimeReciprocalTheorem
import OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem

namespace OAI

/-! All three main statements with the two proved prime-distribution inputs
discharged. Only the circuit and MRT inputs remain parameters. -/

namespace TwoPointCorrelations

theorem liouvilleLogSaving_of_circuit_mrt (hBr : BravermanDepth22Input)
    (hMRT : MRTLiouvilleShortInput) : LiouvilleLogSaving :=
  conditional_liouvilleLogSaving modFiveThetaInput hBr primeReciprocalInput hMRT

theorem binaryCorrectedElliott_of_circuit_mrt (hBr : BravermanDepth22Input)
    (hMRT : MRTShortExponentialInput) : BinaryCorrectedElliott :=
  conditional_binaryCorrectedElliott modFiveThetaInput hBr primeReciprocalInput hMRT

theorem affineCorrectedElliott_of_circuit_mrt (hBr : BravermanDepth22Input)
    (hMRT : MRTShortExponentialInput) : AffineCorrectedElliott :=
  conditional_affineCorrectedElliott modFiveThetaInput hBr primeReciprocalInput hMRT

end TwoPointCorrelations

end OAI
