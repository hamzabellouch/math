import OAI.MathematicalPhysics.Transonic.Certificates.Window00
import OAI.MathematicalPhysics.Transonic.Certificates.Window01
import OAI.MathematicalPhysics.Transonic.Certificates.Window02
import OAI.MathematicalPhysics.Transonic.Certificates.Window03
import OAI.MathematicalPhysics.Transonic.Certificates.Window04
import OAI.MathematicalPhysics.Transonic.Certificates.Window05
import OAI.MathematicalPhysics.Transonic.Certificates.Window06
import OAI.MathematicalPhysics.Transonic.Certificates.Window07

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem group0_produces {t : ℝ} (ht : t∈Set.Icc C00.lo C07.hi)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h0 : t≤C00.hi
  · apply C00.produces ?_ u hu0 hu1 he
    constructor
    · exact ht.1
    · exact h0
  by_cases h1 : t≤C01.hi
  · apply C01.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C01.lo=C00.hi := by norm_num [C01.lo,C00.hi]
      rw [hEq]
      exact (lt_of_not_ge h0).le
    · exact h1
  by_cases h2 : t≤C02.hi
  · apply C02.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C02.lo=C01.hi := by norm_num [C02.lo,C01.hi]
      rw [hEq]
      exact (lt_of_not_ge h1).le
    · exact h2
  by_cases h3 : t≤C03.hi
  · apply C03.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C03.lo=C02.hi := by norm_num [C03.lo,C02.hi]
      rw [hEq]
      exact (lt_of_not_ge h2).le
    · exact h3
  by_cases h4 : t≤C04.hi
  · apply C04.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C04.lo=C03.hi := by norm_num [C04.lo,C03.hi]
      rw [hEq]
      exact (lt_of_not_ge h3).le
    · exact h4
  by_cases h5 : t≤C05.hi
  · apply C05.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C05.lo=C04.hi := by norm_num [C05.lo,C04.hi]
      rw [hEq]
      exact (lt_of_not_ge h4).le
    · exact h5
  by_cases h6 : t≤C06.hi
  · apply C06.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C06.lo=C05.hi := by norm_num [C06.lo,C05.hi]
      rw [hEq]
      exact (lt_of_not_ge h5).le
    · exact h6
  apply C07.produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C07.lo=C06.hi := by norm_num [C07.lo,C06.hi]
    rw [hEq]
    exact (lt_of_not_ge h6).le
  · exact ht.2
end SepticProfile.ExteriorCertificates

end
end

end OAI
