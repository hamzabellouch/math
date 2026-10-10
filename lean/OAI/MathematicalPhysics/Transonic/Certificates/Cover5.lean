import OAI.MathematicalPhysics.Transonic.Certificates.Window40
import OAI.MathematicalPhysics.Transonic.Certificates.Window41
import OAI.MathematicalPhysics.Transonic.Certificates.Window42
import OAI.MathematicalPhysics.Transonic.Certificates.Window43
import OAI.MathematicalPhysics.Transonic.Certificates.Window44
import OAI.MathematicalPhysics.Transonic.Certificates.Window45
import OAI.MathematicalPhysics.Transonic.Certificates.Window46
import OAI.MathematicalPhysics.Transonic.Certificates.Window47

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem group5_produces {t : ℝ} (ht : t∈Set.Icc C40.lo C47.hi)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h40 : t≤C40.hi
  · apply C40.produces ?_ u hu0 hu1 he
    constructor
    · exact ht.1
    · exact h40
  by_cases h41 : t≤C41.hi
  · apply C41.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C41.lo=C40.hi := by norm_num [C41.lo,C40.hi]
      rw [hEq]
      exact (lt_of_not_ge h40).le
    · exact h41
  by_cases h42 : t≤C42.hi
  · apply C42.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C42.lo=C41.hi := by norm_num [C42.lo,C41.hi]
      rw [hEq]
      exact (lt_of_not_ge h41).le
    · exact h42
  by_cases h43 : t≤C43.hi
  · apply C43.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C43.lo=C42.hi := by norm_num [C43.lo,C42.hi]
      rw [hEq]
      exact (lt_of_not_ge h42).le
    · exact h43
  by_cases h44 : t≤C44.hi
  · apply C44.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C44.lo=C43.hi := by norm_num [C44.lo,C43.hi]
      rw [hEq]
      exact (lt_of_not_ge h43).le
    · exact h44
  by_cases h45 : t≤C45.hi
  · apply C45.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C45.lo=C44.hi := by norm_num [C45.lo,C44.hi]
      rw [hEq]
      exact (lt_of_not_ge h44).le
    · exact h45
  by_cases h46 : t≤C46.hi
  · apply C46.produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C46.lo=C45.hi := by norm_num [C46.lo,C45.hi]
      rw [hEq]
      exact (lt_of_not_ge h45).le
    · exact h46
  apply C47.produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C47.lo=C46.hi := by norm_num [C47.lo,C46.hi]
    rw [hEq]
    exact (lt_of_not_ge h46).le
  · exact ht.2
end SepticProfile.ExteriorCertificates

end
end

end OAI
