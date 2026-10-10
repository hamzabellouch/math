import OAI.MathematicalPhysics.Transonic.Certificates.Window48
import OAI.MathematicalPhysics.Transonic.Certificates.Window49
import OAI.MathematicalPhysics.Transonic.Certificates.Window50
import OAI.MathematicalPhysics.Transonic.Certificates.Window51
import OAI.MathematicalPhysics.Transonic.Certificates.Window52
import OAI.MathematicalPhysics.Transonic.Certificates.Window53
import OAI.MathematicalPhysics.Transonic.Certificates.Window54
import OAI.MathematicalPhysics.Transonic.Certificates.Window55

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem group6_produces {t : ℝ} (ht : t∈Set.Icc C48.lo C55.hi)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h48 : t≤C48.hi
  · apply C48.produces ?_ u hu0 hu1 he
    constructor
    · exact ht.1
    · exact h48
  by_cases h49 : t≤C49.hi
  · apply C49.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C49.lo=C48.hi := by norm_num [C49.lo,C48.hi]
      rw [hEq]
      exact (lt_of_not_ge h48).le
    · exact h49
  by_cases h50 : t≤C50.hi
  · apply C50.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C50.lo=C49.hi := by norm_num [C50.lo,C49.hi]
      rw [hEq]
      exact (lt_of_not_ge h49).le
    · exact h50
  by_cases h51 : t≤C51.hi
  · apply C51.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C51.lo=C50.hi := by norm_num [C51.lo,C50.hi]
      rw [hEq]
      exact (lt_of_not_ge h50).le
    · exact h51
  by_cases h52 : t≤C52.hi
  · apply C52.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C52.lo=C51.hi := by norm_num [C52.lo,C51.hi]
      rw [hEq]
      exact (lt_of_not_ge h51).le
    · exact h52
  by_cases h53 : t≤C53.hi
  · apply C53.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C53.lo=C52.hi := by norm_num [C53.lo,C52.hi]
      rw [hEq]
      exact (lt_of_not_ge h52).le
    · exact h53
  by_cases h54 : t≤C54.hi
  · apply C54.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C54.lo=C53.hi := by norm_num [C54.lo,C53.hi]
      rw [hEq]
      exact (lt_of_not_ge h53).le
    · exact h54
  apply C55.produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C55.lo=C54.hi := by norm_num [C55.lo,C54.hi]
    rw [hEq]
    exact (lt_of_not_ge h54).le
  · exact ht.2
end SepticProfile.ExteriorCertificates

end
end

end OAI
