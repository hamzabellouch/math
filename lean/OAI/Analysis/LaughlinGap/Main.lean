import Mathlib
import OAI.Analysis.LaughlinGap.Certificate10
import OAI.Analysis.LaughlinGap.Certificate12
import OAI.Analysis.LaughlinGap.Certificate14
import OAI.Analysis.LaughlinGap.Certificate16
import OAI.Analysis.LaughlinGap.Certificate18
import OAI.Analysis.LaughlinGap.Certificate20
import OAI.Analysis.LaughlinGap.Certificate22
import OAI.Analysis.LaughlinGap.Certificate23
import OAI.Analysis.LaughlinGap.Certificate6
import OAI.Analysis.LaughlinGap.Certificate8
import OAI.Analysis.LaughlinGap.GlobalBound
import OAI.Analysis.LaughlinGap.ZeroCertificates

namespace OAI

/-! Main. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators

lemma exact_four (d : Fin 23) :
    FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000)
      (d.val+1) (by omega) := by
  fin_cases d
  · exact certificate_1
  · exact certificate_2
  · exact certificate_3
  · exact certificate_4
  · exact Certificate5.certificate
  · exact Certificate6.certificate
  · exact Certificate7.certificate
  · exact Certificate8.certificate
  · exact Certificate9.certificate
  · exact Certificate10.certificate
  · exact Certificate11.certificate
  · exact Certificate12.certificate
  · exact Certificate13.certificate
  · exact Certificate14.certificate
  · exact Certificate15.certificate
  · exact Certificate16.certificate
  · exact Certificate17.certificate
  · exact Certificate18.certificate
  · exact Certificate19.certificate
  · exact Certificate20.certificate
  · exact Certificate21.certificate
  · exact Certificate22.certificate
  · exact Certificate23.certificate

end LaughlinGap.RealOccupation

namespace LaughlinGap

theorem thm_main : MainTarget := by
  exact RealOccupation.mainTarget_of_finite_certificates
    (fun a : Fin 8 => (RealOccupation.exactRows a).toReal) (1/200000)
    (by norm_num) RealOccupation.exact_margin RealOccupation.exact_three
    RealOccupation.exact_four

end LaughlinGap

end

end OAI
