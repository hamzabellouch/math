import OAI.MathematicalPhysics.Transonic.Certificates.Window08
import OAI.MathematicalPhysics.Transonic.Certificates.Window09
import OAI.MathematicalPhysics.Transonic.Certificates.Window10
import OAI.MathematicalPhysics.Transonic.Certificates.Window11
import OAI.MathematicalPhysics.Transonic.Certificates.Window12
import OAI.MathematicalPhysics.Transonic.Certificates.Window13
import OAI.MathematicalPhysics.Transonic.Certificates.Window14
import OAI.MathematicalPhysics.Transonic.Certificates.Window15

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem group1_produces {t : ℝ} (ht : t∈Set.Icc C08.lo C15.hi)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h8 : t≤C08.hi
  · apply C08.produces ?_ u hu0 hu1 he
    constructor
    · exact ht.1
    · exact h8
  by_cases h9 : t≤C09.hi
  · apply C09.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C09.lo=C08.hi := by norm_num [C09.lo,C08.hi]
      rw [hEq]
      exact (lt_of_not_ge h8).le
    · exact h9
  by_cases h10 : t≤C10.hi
  · apply C10.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C10.lo=C09.hi := by norm_num [C10.lo,C09.hi]
      rw [hEq]
      exact (lt_of_not_ge h9).le
    · exact h10
  by_cases h11 : t≤C11.hi
  · apply C11.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C11.lo=C10.hi := by norm_num [C11.lo,C10.hi]
      rw [hEq]
      exact (lt_of_not_ge h10).le
    · exact h11
  by_cases h12 : t≤C12.hi
  · apply C12.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C12.lo=C11.hi := by norm_num [C12.lo,C11.hi]
      rw [hEq]
      exact (lt_of_not_ge h11).le
    · exact h12
  by_cases h13 : t≤C13.hi
  · apply C13.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C13.lo=C12.hi := by norm_num [C13.lo,C12.hi]
      rw [hEq]
      exact (lt_of_not_ge h12).le
    · exact h13
  by_cases h14 : t≤C14.hi
  · apply C14.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C14.lo=C13.hi := by norm_num [C14.lo,C13.hi]
      rw [hEq]
      exact (lt_of_not_ge h13).le
    · exact h14
  apply C15.produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C15.lo=C14.hi := by norm_num [C15.lo,C14.hi]
    rw [hEq]
    exact (lt_of_not_ge h14).le
  · exact ht.2
end SepticProfile.ExteriorCertificates

end
end

end OAI
