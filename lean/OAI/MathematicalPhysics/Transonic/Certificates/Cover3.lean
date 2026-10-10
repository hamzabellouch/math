import OAI.MathematicalPhysics.Transonic.Certificates.Window24
import OAI.MathematicalPhysics.Transonic.Certificates.Window25
import OAI.MathematicalPhysics.Transonic.Certificates.Window26
import OAI.MathematicalPhysics.Transonic.Certificates.Window27
import OAI.MathematicalPhysics.Transonic.Certificates.Window28
import OAI.MathematicalPhysics.Transonic.Certificates.Window29
import OAI.MathematicalPhysics.Transonic.Certificates.Window30
import OAI.MathematicalPhysics.Transonic.Certificates.Window31

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem group3_produces {t : ℝ} (ht : t∈Set.Icc C24.lo C31.hi)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h24 : t≤C24.hi
  · apply C24.produces ?_ u hu0 hu1 he
    constructor
    · exact ht.1
    · exact h24
  by_cases h25 : t≤C25.hi
  · apply C25.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C25.lo=C24.hi := by norm_num [C25.lo,C24.hi]
      rw [hEq]
      exact (lt_of_not_ge h24).le
    · exact h25
  by_cases h26 : t≤C26.hi
  · apply C26.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C26.lo=C25.hi := by norm_num [C26.lo,C25.hi]
      rw [hEq]
      exact (lt_of_not_ge h25).le
    · exact h26
  by_cases h27 : t≤C27.hi
  · apply C27.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C27.lo=C26.hi := by norm_num [C27.lo,C26.hi]
      rw [hEq]
      exact (lt_of_not_ge h26).le
    · exact h27
  by_cases h28 : t≤C28.hi
  · apply C28.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C28.lo=C27.hi := by norm_num [C28.lo,C27.hi]
      rw [hEq]
      exact (lt_of_not_ge h27).le
    · exact h28
  by_cases h29 : t≤C29.hi
  · apply C29.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C29.lo=C28.hi := by norm_num [C29.lo,C28.hi]
      rw [hEq]
      exact (lt_of_not_ge h28).le
    · exact h29
  by_cases h30 : t≤C30.hi
  · apply C30.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C30.lo=C29.hi := by norm_num [C30.lo,C29.hi]
      rw [hEq]
      exact (lt_of_not_ge h29).le
    · exact h30
  apply C31.produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C31.lo=C30.hi := by norm_num [C31.lo,C30.hi]
    rw [hEq]
    exact (lt_of_not_ge h30).le
  · exact ht.2
end SepticProfile.ExteriorCertificates

end
end

end OAI
