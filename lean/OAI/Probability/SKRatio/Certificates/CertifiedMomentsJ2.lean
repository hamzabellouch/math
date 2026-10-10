import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedConstants
import OAI.Probability.SKRatio.Certificates.CertifiedMomentAssembly
import OAI.Probability.SKRatio.Certificates.ScalarDataJ2K0
import OAI.Probability.SKRatio.Certificates.ScalarDataJ2K1
import OAI.Probability.SKRatio.Certificates.ScalarDataJ2K2
import OAI.Probability.SKRatio.Certificates.ScalarDataJ2K3
import OAI.Probability.SKRatio.Certificates.ScalarDataJ2K4
import OAI.Probability.SKRatio.Certificates.ScalarDataJ2K5
import OAI.Probability.SKRatio.Certificates.ScalarDataJ2K6
import OAI.Probability.SKRatio.Certificates.ScalarDataJ2K7

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

theorem valid2 : Valid (89/200) X2 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Data.J2K0.integral_bound
  · exact Data.J2K1.integral_bound
  · exact Data.J2K2.integral_bound
  · exact Data.J2K3.integral_bound
  · apply mem_sd_center memLp_v (c := (52021/62500)) (by norm_num : (0:ℚ) ≤ 181/1000)
    convert! Data.J2K4.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_g (c := (13423/25000)) (by norm_num : (0:ℚ) ≤ 103/1000)
    convert! Data.J2K5.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_mv (c := (21477/200000)) (by norm_num : (0:ℚ) ≤ 127/500)
    convert! Data.J2K6.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_F_of_center (A := (52021/62500)) (C := (13423/25000)) (Q := (81561/125000))
      (sa := (789/1000)) (sf := (397/500)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    · convert! Data.J2K0.integral_bound using 1; norm_num [scalarFunction,a]
    · convert! Data.J2K1.integral_bound using 1; norm_num [scalarFunction,G]
    · norm_num
    · convert! Data.J2K7.integral_bound using 1 <;> norm_num [scalarFunction]
    · norm_num

end SKRatio.Certificate

end

end OAI
