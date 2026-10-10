import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedConstants
import OAI.Probability.SKRatio.Certificates.CertifiedMomentAssembly
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K0
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K1
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K2
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K3
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K4
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K5
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K6
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K7

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

theorem valid4 : Valid (1/2) X4 := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Data.J4K0.integral_bound
  · exact Data.J4K1.integral_bound
  · exact Data.J4K2.integral_bound
  · exact Data.J4K3.integral_bound
  · apply mem_sd_center memLp_v (c := (397973/500000)) (by norm_num : (0:ℚ) ≤ 209/1000)
    convert! Data.J4K4.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_g (c := (524071/1000000)) (by norm_num : (0:ℚ) ≤ 23/200)
    convert! Data.J4K5.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_sd_center memLp_mv (c := (119553/1000000)) (by norm_num : (0:ℚ) ≤ 257/1000)
    convert! Data.J4K6.integral_bound using 1 <;> norm_num [scalarFunction]
  · apply mem_F_of_center (A := (397973/500000)) (C := (524071/1000000)) (Q := (702377/1000000))
      (sa := (17/20)) (sf := (171/200)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    · convert! Data.J4K0.integral_bound using 1
      norm_num [scalarFunction,a]
    · convert! Data.J4K1.integral_bound using 1
      norm_num [scalarFunction,G]
    · norm_num
    · convert! Data.J4K7.integral_bound using 1 <;> norm_num [scalarFunction]
    · norm_num

end SKRatio.Certificate

end

end OAI
