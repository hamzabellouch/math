import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedConstants
import OAI.Probability.SKRatio.Certificates.CertifiedMomentAssembly
import OAI.Probability.SKRatio.Certificates.ScalarDataJ3K0
import OAI.Probability.SKRatio.Certificates.ScalarDataJ3K1
import OAI.Probability.SKRatio.Certificates.ScalarDataJ3K2
import OAI.Probability.SKRatio.Certificates.ScalarDataJ3K3
import OAI.Probability.SKRatio.Certificates.ScalarDataJ3K4
import OAI.Probability.SKRatio.Certificates.ScalarDataJ3K5
import OAI.Probability.SKRatio.Certificates.ScalarDataJ3K6
import OAI.Probability.SKRatio.Certificates.ScalarDataJ3K7

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

theorem valid3 : Valid (19/40) X3 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Data.J3K0.integral_bound
  · exact Data.J3K1.integral_bound
  · exact Data.J3K2.integral_bound
  · exact Data.J3K3.integral_bound
  · apply mem_sd_center memLp_v (c := (406349/500000)) (by norm_num : (0:ℚ) ≤ 49/250)
    convert! Data.J3K4.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_g (c := (66273/125000)) (by norm_num : (0:ℚ) ≤ 109/1000)
    convert! Data.J3K5.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_mv (c := (28579/250000)) (by norm_num : (0:ℚ) ≤ 32/125)
    convert! Data.J3K6.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_F_of_center (A := (406349/500000)) (C := (66273/125000)) (Q := (135787/200000))
      (sa := (823/1000)) (sf := (207/250)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    · convert! Data.J3K0.integral_bound using 1
      norm_num [scalarFunction,a]
    · convert! Data.J3K1.integral_bound using 1
      norm_num [scalarFunction,G]
    · norm_num
    · convert! Data.J3K7.integral_bound using 1 <;> norm_num [scalarFunction]
    · norm_num

end SKRatio.Certificate

end

end OAI
