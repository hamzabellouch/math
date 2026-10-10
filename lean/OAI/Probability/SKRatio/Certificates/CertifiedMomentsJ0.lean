import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedConstants
import OAI.Probability.SKRatio.Certificates.CertifiedMomentAssembly
import OAI.Probability.SKRatio.Certificates.ScalarDataJ0K0
import OAI.Probability.SKRatio.Certificates.ScalarDataJ0K1
import OAI.Probability.SKRatio.Certificates.ScalarDataJ0K2
import OAI.Probability.SKRatio.Certificates.ScalarDataJ0K3
import OAI.Probability.SKRatio.Certificates.ScalarDataJ0K4
import OAI.Probability.SKRatio.Certificates.ScalarDataJ0K5
import OAI.Probability.SKRatio.Certificates.ScalarDataJ0K6
import OAI.Probability.SKRatio.Certificates.ScalarDataJ0K7

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

theorem valid0 : Valid (7/20) X0 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Data.J0K0.integral_bound
  · exact Data.J0K1.integral_bound
  · exact Data.J0K2.integral_bound
  · exact Data.J0K3.integral_bound
  · apply mem_sd_center memLp_v (c := (44507/50000)) (by norm_num : (0:ℚ) ≤ 13/100)
    convert! Data.J0K4.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_g (c := (110763/200000)) (by norm_num : (0:ℚ) ≤ 43/500)
    convert! Data.J0K5.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_mv (c := (20333/250000)) (by norm_num : (0:ℚ) ≤ 239/1000)
    convert! Data.J0K6.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_F_of_center (A := (44507/50000)) (C := (110763/200000)) (Q := (14573/25000))
      (sa := (661/1000)) (sf := (333/500)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    · convert! Data.J0K0.integral_bound using 1
      norm_num [scalarFunction,a]
    · convert! Data.J0K1.integral_bound using 1
      norm_num [scalarFunction,G]
    · norm_num
    · convert! Data.J0K7.integral_bound using 1 <;> norm_num [scalarFunction]
    · norm_num

end SKRatio.Certificate

end

end OAI
