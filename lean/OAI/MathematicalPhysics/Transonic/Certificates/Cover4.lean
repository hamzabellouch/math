import OAI.MathematicalPhysics.Transonic.Certificates.Window32
import OAI.MathematicalPhysics.Transonic.Certificates.Window33
import OAI.MathematicalPhysics.Transonic.Certificates.Window34
import OAI.MathematicalPhysics.Transonic.Certificates.Window35
import OAI.MathematicalPhysics.Transonic.Certificates.Window36
import OAI.MathematicalPhysics.Transonic.Certificates.Window37
import OAI.MathematicalPhysics.Transonic.Certificates.Window38
import OAI.MathematicalPhysics.Transonic.Certificates.Window39

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem group4_produces {t : ℝ} (ht : t∈Set.Icc C32.lo C39.hi)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h32 : t≤C32.hi
  · apply C32.produces ?_ u hu0 hu1 he
    constructor
    · exact ht.1
    · exact h32
  by_cases h33 : t≤C33.hi
  · apply C33.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C33.lo=C32.hi := by norm_num [C33.lo,C32.hi]
      rw [hEq]
      exact (lt_of_not_ge h32).le
    · exact h33
  by_cases h34 : t≤C34.hi
  · apply C34.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C34.lo=C33.hi := by norm_num [C34.lo,C33.hi]
      rw [hEq]
      exact (lt_of_not_ge h33).le
    · exact h34
  by_cases h35 : t≤C35.hi
  · apply C35.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C35.lo=C34.hi := by norm_num [C35.lo,C34.hi]
      rw [hEq]
      exact (lt_of_not_ge h34).le
    · exact h35
  by_cases h36 : t≤C36.hi
  · apply C36.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C36.lo=C35.hi := by norm_num [C36.lo,C35.hi]
      rw [hEq]
      exact (lt_of_not_ge h35).le
    · exact h36
  by_cases h37 : t≤C37.hi
  · apply C37.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C37.lo=C36.hi := by norm_num [C37.lo,C36.hi]
      rw [hEq]
      exact (lt_of_not_ge h36).le
    · exact h37
  by_cases h38 : t≤C38.hi
  · apply C38.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C38.lo=C37.hi := by norm_num [C38.lo,C37.hi]
      rw [hEq]
      exact (lt_of_not_ge h37).le
    · exact h38
  apply C39.produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C39.lo=C38.hi := by norm_num [C39.lo,C38.hi]
    rw [hEq]
    exact (lt_of_not_ge h38).le
  · exact ht.2
end SepticProfile.ExteriorCertificates

end
end

end OAI
