import OAI.MathematicalPhysics.Transonic.Certificates.Window56
import OAI.MathematicalPhysics.Transonic.Certificates.Window57
import OAI.MathematicalPhysics.Transonic.Certificates.Window58
import OAI.MathematicalPhysics.Transonic.Certificates.Window59
import OAI.MathematicalPhysics.Transonic.Certificates.Window60
import OAI.MathematicalPhysics.Transonic.Certificates.Window61
import OAI.MathematicalPhysics.Transonic.Certificates.Window62
import OAI.MathematicalPhysics.Transonic.Certificates.Window63

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem group7_produces {t : ℝ} (ht : t∈Set.Icc C56.lo C63.hi)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h56 : t≤C56.hi
  · apply C56.produces ?_ u hu0 hu1 he
    constructor
    · exact ht.1
    · exact h56
  by_cases h57 : t≤C57.hi
  · apply C57.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C57.lo=C56.hi := by norm_num [C57.lo,C56.hi]
      rw [hEq]
      exact (lt_of_not_ge h56).le
    · exact h57
  by_cases h58 : t≤C58.hi
  · apply C58.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C58.lo=C57.hi := by norm_num [C58.lo,C57.hi]
      rw [hEq]
      exact (lt_of_not_ge h57).le
    · exact h58
  by_cases h59 : t≤C59.hi
  · apply C59.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C59.lo=C58.hi := by norm_num [C59.lo,C58.hi]
      rw [hEq]
      exact (lt_of_not_ge h58).le
    · exact h59
  by_cases h60 : t≤C60.hi
  · apply C60.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C60.lo=C59.hi := by norm_num [C60.lo,C59.hi]
      rw [hEq]
      exact (lt_of_not_ge h59).le
    · exact h60
  by_cases h61 : t≤C61.hi
  · apply C61.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C61.lo=C60.hi := by norm_num [C61.lo,C60.hi]
      rw [hEq]
      exact (lt_of_not_ge h60).le
    · exact h61
  by_cases h62 : t≤C62.hi
  · apply C62.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C62.lo=C61.hi := by norm_num [C62.lo,C61.hi]
      rw [hEq]
      exact (lt_of_not_ge h61).le
    · exact h62
  apply C63.produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C63.lo=C62.hi := by norm_num [C63.lo,C62.hi]
    rw [hEq]
    exact (lt_of_not_ge h62).le
  · exact ht.2
end SepticProfile.ExteriorCertificates

end
end

end OAI
