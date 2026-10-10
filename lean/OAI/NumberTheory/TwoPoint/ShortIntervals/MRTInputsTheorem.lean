import OAI.NumberTheory.TwoPoint.Halasz.HalaszWeakHurwitzTheorem
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRieszEstimate
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKTheorem

namespace OAI

/-! The corrected short exponential-sum estimates of Matomäki, Radziwiłł,
and Tao in the specializations used for ordinary two-point correlations. -/
namespace TwoPointCorrelations

/-- Corrected MRT (2015), Theorem 1.7, in the application specialization. -/
theorem mrtShortExponentialInput : MRTShortExponentialInput :=
  mrt_weak_hurwitz_growth.short_exponential mrt_weak_hurwitz_growth.prime_sparse

/-- Corrected MRT (2015), Theorem 1.3, in the application specialization. -/
theorem mrtLiouvilleShortInput : MRTLiouvilleShortInput :=
  mrt_weak_hurwitz_growth.liouville_short mrt_weak_hurwitz_growth.prime_sparse

end TwoPointCorrelations

end OAI
