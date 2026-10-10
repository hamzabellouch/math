import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTInputsTheorem
import OAI.NumberTheory.TwoPoint.MainWithMRTInputs

namespace OAI

/-! Paper 009-01: the three original main results, unconditionally. -/
namespace TwoPointCorrelations

/-- Theorem 1.1: ordinary Liouville correlations with an absolute logarithmic saving. -/
theorem liouvilleLogSaving : LiouvilleLogSaving :=
  liouvilleLogSaving_of_mrt mrtLiouvilleShortInput

/-- Theorem 1.2: the binary corrected Elliott theorem. -/
theorem binaryCorrectedElliott : BinaryCorrectedElliott :=
  binaryCorrectedElliott_of_mrt mrtShortExponentialInput

/-- Corollary 1.3: the corrected Elliott theorem for nonproportional affine forms. -/
theorem affineCorrectedElliott : AffineCorrectedElliott :=
  affineCorrectedElliott_of_mrt mrtShortExponentialInput

end TwoPointCorrelations

end OAI
