import Mathlib
import OAI.Probability.SKRatio.Certificates.CertifiedEndpointAssembly
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K8
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K9
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K10
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K11
import OAI.Probability.SKRatio.Certificates.ScalarDataJ4K12

namespace OAI

noncomputable section
open Real MeasureTheory
namespace SKRatio.Certificate
open Scalar

lemma endpointK_zero_bound : endpointK 0 ≤ 4280/10000 := by
  rw [endpointK_zero_integral (1/2) (397973/500000) (524071/1000000)
    (119553/1000000) (702377/1000000)]
  convert! Data.J4K8.integral_bound.2 using 1; norm_num

lemma endpointK_one_bound : endpointK 1 ≤ 902/10000 := by
  rw [endpointK_one_integral (1/2) (397973/500000) (524071/1000000)
    (119553/1000000) (702377/1000000)]
  convert! Data.J4K9.integral_bound.2 using 1; norm_num

lemma endpointD_zero_bound : endpointD 0 ≤ 929/10000 := by
  rw [endpointD_zero_integral (1/2) (397973/500000) (524071/1000000)
    (119553/1000000) (702377/1000000)]
  convert! Data.J4K10.integral_bound.2 using 1; norm_num

lemma endpointD_one_bound : endpointD 1 ≤ 2292/10000 := by
  rw [endpointD_one_integral (1/2) (397973/500000) (524071/1000000)
    (119553/1000000) (702377/1000000)]
  convert! Data.J4K12.integral_bound.2 using 1; norm_num

lemma endpointD_prime_lower : 520/10000 ≤ endpointDPrime := by
  rw [endpointD_prime_integral (1/2) (397973/500000) (524071/1000000)
    (119553/1000000) (702377/1000000)]
  convert! Data.J4K11.integral_bound.1 using 1; norm_num

lemma endpointD_prime_upper : endpointDPrime ≤ 526/10000 := by
  rw [endpointD_prime_integral (1/2) (397973/500000) (524071/1000000)
    (119553/1000000) (702377/1000000)]
  convert! Data.J4K11.integral_bound.2 using 1; norm_num

theorem diagonal_envelope {β : ℝ} (hβ : 0 < β) (hβh : β ≤ 1/2) (h : ℝ) :
    multiplier h+diagonal (fieldLaw β) β h+cost (fieldLaw β) β h ≤ 9789/10000 :=
  envelope_of_endpoint_data endpointK_zero_bound endpointK_one_bound
    endpointD_zero_bound endpointD_one_bound endpointD_prime_lower endpointD_prime_upper
    hβ hβh h

end SKRatio.Certificate

end

end OAI
