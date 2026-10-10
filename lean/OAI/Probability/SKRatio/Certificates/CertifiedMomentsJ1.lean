import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedConstants
import OAI.Probability.SKRatio.Certificates.CertifiedMomentAssembly
import OAI.Probability.SKRatio.Certificates.ScalarDataJ1K0
import OAI.Probability.SKRatio.Certificates.ScalarDataJ1K1
import OAI.Probability.SKRatio.Certificates.ScalarDataJ1K2
import OAI.Probability.SKRatio.Certificates.ScalarDataJ1K3
import OAI.Probability.SKRatio.Certificates.ScalarDataJ1K4
import OAI.Probability.SKRatio.Certificates.ScalarDataJ1K5
import OAI.Probability.SKRatio.Certificates.ScalarDataJ1K6
import OAI.Probability.SKRatio.Certificates.ScalarDataJ1K7

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

theorem valid1 : Valid (2/5) X1 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Data.J1K0.integral_bound
  · exact Data.J1K1.integral_bound
  · exact Data.J1K2.integral_bound
  · exact Data.J1K3.integral_bound
  · apply mem_sd_center memLp_v (c := (107581/125000)) (by norm_num : (0:ℚ) ≤ 157/1000)
    convert! Data.J1K4.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_g (c := (545767/1000000)) (by norm_num : (0:ℚ) ≤ 19/200)
    convert! Data.J1K5.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_mv (c := (95751/1000000)) (by norm_num : (0:ℚ) ≤ 249/1000)
    convert! Data.J1K6.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_F_of_center (A := (107581/125000)) (C := (545767/1000000)) (Q := (616697/1000000))
      (sa := (183/250)) (sf := (737/1000)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    · convert! Data.J1K0.integral_bound using 1
      norm_num [scalarFunction,a]
    · convert! Data.J1K1.integral_bound using 1
      norm_num [scalarFunction,G]
    · norm_num
    · convert! Data.J1K7.integral_bound using 1 <;> norm_num [scalarFunction]
    · norm_num

end SKRatio.Certificate

end

end OAI
