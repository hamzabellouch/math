import OAI.MathematicalPhysics.Transonic.Certificates.Window16
import OAI.MathematicalPhysics.Transonic.Certificates.Window17
import OAI.MathematicalPhysics.Transonic.Certificates.Window18
import OAI.MathematicalPhysics.Transonic.Certificates.Window19
import OAI.MathematicalPhysics.Transonic.Certificates.Window20
import OAI.MathematicalPhysics.Transonic.Certificates.Window21
import OAI.MathematicalPhysics.Transonic.Certificates.Window22
import OAI.MathematicalPhysics.Transonic.Certificates.Window23

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem group2_produces {t : ℝ} (ht : t∈Set.Icc C16.lo C23.hi)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h16 : t≤C16.hi
  · apply C16.produces ?_ u hu0 hu1 he
    constructor
    · exact ht.1
    · exact h16
  by_cases h17 : t≤C17.hi
  · apply C17.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C17.lo=C16.hi := by norm_num [C17.lo,C16.hi]
      rw [hEq]
      exact (lt_of_not_ge h16).le
    · exact h17
  by_cases h18 : t≤C18.hi
  · apply C18.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C18.lo=C17.hi := by norm_num [C18.lo,C17.hi]
      rw [hEq]
      exact (lt_of_not_ge h17).le
    · exact h18
  by_cases h19 : t≤C19.hi
  · apply C19.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C19.lo=C18.hi := by norm_num [C19.lo,C18.hi]
      rw [hEq]
      exact (lt_of_not_ge h18).le
    · exact h19
  by_cases h20 : t≤C20.hi
  · apply C20.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C20.lo=C19.hi := by norm_num [C20.lo,C19.hi]
      rw [hEq]
      exact (lt_of_not_ge h19).le
    · exact h20
  by_cases h21 : t≤C21.hi
  · apply C21.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C21.lo=C20.hi := by norm_num [C21.lo,C20.hi]
      rw [hEq]
      exact (lt_of_not_ge h20).le
    · exact h21
  by_cases h22 : t≤C22.hi
  · apply C22.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C22.lo=C21.hi := by norm_num [C22.lo,C21.hi]
      rw [hEq]
      exact (lt_of_not_ge h21).le
    · exact h22
  apply C23.produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C23.lo=C22.hi := by norm_num [C23.lo,C22.hi]
    rw [hEq]
    exact (lt_of_not_ge h22).le
  · exact ht.2
end SepticProfile.ExteriorCertificates

end
end

end OAI
