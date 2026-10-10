import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakVKApplications

namespace OAI

/-! Conditional assembly from the precise weak Hurwitz growth statement
and the still-explicit sparse prime mean-square input. -/

namespace TwoPointCorrelations

theorem MRTWeakHurwitzGrowthInput.short_exponential (h : MRTWeakHurwitzGrowthInput)
    (hprime : HalaszPrimeSparseInput) : MRTShortExponentialInput :=
  mrt_short_exponential_of_prime_estimates hprime h.high_prime

theorem MRTWeakHurwitzGrowthInput.liouville_short (h : MRTWeakHurwitzGrowthInput)
    (hprime : HalaszPrimeSparseInput) : MRTLiouvilleShortInput :=
  mrt_liouville_short_of_distance (h.short_exponential hprime) h.liouville_distance

end TwoPointCorrelations

end OAI
