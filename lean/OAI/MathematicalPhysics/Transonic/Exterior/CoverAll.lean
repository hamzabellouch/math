import OAI.MathematicalPhysics.Transonic.Certificates.Cover0
import OAI.MathematicalPhysics.Transonic.Certificates.Cover1
import OAI.MathematicalPhysics.Transonic.Certificates.Cover2
import OAI.MathematicalPhysics.Transonic.Certificates.Cover3
import OAI.MathematicalPhysics.Transonic.Certificates.Cover4
import OAI.MathematicalPhysics.Transonic.Certificates.Cover5
import OAI.MathematicalPhysics.Transonic.Certificates.Cover6
import OAI.MathematicalPhysics.Transonic.Certificates.Cover7
import OAI.MathematicalPhysics.Transonic.Shooting.ExteriorGermEntry

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
theorem produces {t : ℝ} (ht : t∈Set.Icc ShootingParameters.leftEnd ShootingParameters.rightEnd)
    (u : PowerSeries ℝ) (hu0 : PowerSeries.coeff 0 u=1)
    (hu1 : PowerSeries.coeff 1 u=ShootingParameters.slope t)
    (he : Formal.residual (ShootingParameters.sigma t) (ShootingParameters.kappa t) (3/5) u=0) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (ShootingParameters.sigma t)
      (ShootingParameters.kappa t) d u) ∧ 0<PowerSeries.coeff 74 u := by
  by_cases h0 : t≤C07.hi
  · apply group0_produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C00.lo=ShootingParameters.leftEnd := by norm_num [C00.lo,ShootingParameters.leftEnd]
      rw [hEq]
      exact ht.1
    · exact h0
  by_cases h1 : t≤C15.hi
  · apply group1_produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C08.lo=C07.hi := by norm_num [C08.lo,C07.hi]
      rw [hEq]
      exact (lt_of_not_ge h0).le
    · exact h1
  by_cases h2 : t≤C23.hi
  · apply group2_produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C16.lo=C15.hi := by norm_num [C16.lo,C15.hi]
      rw [hEq]
      exact (lt_of_not_ge h1).le
    · exact h2
  by_cases h3 : t≤C31.hi
  · apply group3_produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C24.lo=C23.hi := by norm_num [C24.lo,C23.hi]
      rw [hEq]
      exact (lt_of_not_ge h2).le
    · exact h3
  by_cases h4 : t≤C39.hi
  · apply group4_produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C32.lo=C31.hi := by norm_num [C32.lo,C31.hi]
      rw [hEq]
      exact (lt_of_not_ge h3).le
    · exact h4
  by_cases h5 : t≤C47.hi
  · apply group5_produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C40.lo=C39.hi := by norm_num [C40.lo,C39.hi]
      rw [hEq]
      exact (lt_of_not_ge h4).le
    · exact h5
  by_cases h6 : t≤C55.hi
  · apply group6_produces ?_ u hu0 hu1 he
    constructor
    · have hEq : C48.lo=C47.hi := by norm_num [C48.lo,C47.hi]
      rw [hEq]
      exact (lt_of_not_ge h5).le
    · exact h6
  apply group7_produces ?_ u hu0 hu1 he
  constructor
  · have hEq : C56.lo=C55.hi := by norm_num [C56.lo,C55.hi]
    rw [hEq]
    exact (lt_of_not_ge h6).le
  · have hEq : C63.hi=ShootingParameters.rightEnd := by norm_num [C63.hi,ShootingParameters.rightEnd]
    rw [hEq]
    exact ht.2

theorem actual_germ_window (G : SourceFamily.UniformGerm) (p : SourceFamily.Parameter) :
    (∃ d : ℝ, ExteriorPolynomial.AdmissibleWindow (SourceFamily.sig p) (SourceFamily.kap p) d
      (SonicJet.jet (G.realFunction p))) ∧ 0<PowerSeries.coeff 74 (SonicJet.jet (G.realFunction p)) := by
  obtain ⟨h0,h1,he⟩ := G.jet_data p
  exact produces p.property (SonicJet.jet (G.realFunction p)) h0 h1 he

end SepticProfile.ExteriorCertificates

end
end

end OAI
