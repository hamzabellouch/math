import Mathlib
import OAI.Analysis.LaughlinFock.Assembly
import OAI.Analysis.LaughlinFock.Certificate01
import OAI.Analysis.LaughlinFock.Certificate02
import OAI.Analysis.LaughlinFock.Certificate03
import OAI.Analysis.LaughlinFock.Certificate04
import OAI.Analysis.LaughlinFock.Certificate05
import OAI.Analysis.LaughlinFock.Certificate06
import OAI.Analysis.LaughlinFock.Certificate07
import OAI.Analysis.LaughlinFock.Certificate08
import OAI.Analysis.LaughlinFock.Certificate09
import OAI.Analysis.LaughlinFock.Certificate10
import OAI.Analysis.LaughlinFock.Certificate11
import OAI.Analysis.LaughlinFock.Certificate12
import OAI.Analysis.LaughlinFock.Certificate13
import OAI.Analysis.LaughlinFock.Certificate14
import OAI.Analysis.LaughlinFock.Certificate15
import OAI.Analysis.LaughlinFock.Certificate16
import OAI.Analysis.LaughlinFock.Certificate17
import OAI.Analysis.LaughlinFock.Certificate18
import OAI.Analysis.LaughlinFock.Certificate19
import OAI.Analysis.LaughlinFock.Certificate20
import OAI.Analysis.LaughlinFock.Certificate21
import OAI.Analysis.LaughlinFock.Certificate22
import OAI.Analysis.LaughlinFock.Certificate23
import OAI.Analysis.LaughlinFock.IntegerCompression
import OAI.Analysis.LaughlinFock.ThreeCertificate

namespace OAI

/-! Main. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem certificate_four (D : ℕ) (hD : 1 ≤ D) (hD' : D ≤ 23) :
    (planarFourGram D * planarFourComparison certificateRows (3/10^6) D *
      planarFourGram D).PosSemidef := by
  apply planar_certificate_of_integer D
  interval_cases D
  · exact integer_certificate_1
  · exact integer_certificate_2
  · exact integer_certificate_3
  · exact integer_certificate_4
  · exact integer_certificate_5
  · exact integer_certificate_6
  · exact integer_certificate_7
  · exact integer_certificate_8
  · exact integer_certificate_9
  · exact integer_certificate_10
  · exact integer_certificate_11
  · exact integer_certificate_12
  · exact integer_certificate_13
  · exact integer_certificate_14
  · exact integer_certificate_15
  · exact integer_certificate_16
  · exact integer_certificate_17
  · exact integer_certificate_18
  · exact integer_certificate_19
  · exact integer_certificate_20
  · exact integer_certificate_21
  · exact integer_certificate_22
  · exact integer_certificate_23

 

theorem thm_fock (γ : ℝ) (_hγ : 0 < γ) (hγStar : γ < gammaStar) :
    ∃ Qγ : ℤ, 1 ≤ Qγ ∧ ∀ Q : ℤ, Qγ ≤ Q → FockInequality Q.toNat γ := by
  exact integer_threshold_of_certificates_le certificateRows certificateEta_le
    certificate_three certificate_four γ hγStar

end LaughlinFock
end

end OAI
