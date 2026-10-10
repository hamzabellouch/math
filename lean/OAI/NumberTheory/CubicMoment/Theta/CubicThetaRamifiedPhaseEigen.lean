import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPhaseRows

namespace OAI

/-! The explicit modulus-nine phase is an eigenvector of the actual
middle-row operator, with eigenvalue two thirds. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

theorem cubicThetaRamifiedMiddle_phase_eigen {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    (∑' e : Eisensteinˣ,
      cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))*
        cubicThetaNinePhase ((omegaE^(j:ℕ)*(e:Eisenstein))^2*h))=
      (2/3:ℂ)*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
  let : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
  let F (e : Eisensteinˣ) :=
    cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*(e:Eisenstein))^2*h)
  have hclass := cubicThetaLambda_dvd_primary_omega_sub_one hh j
  have hfirst : F cubicThetaOmegaUnit=(1/3:ℂ)*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
    dsimp only [F]
    rw [cubicThetaRamifiedMiddle_first hclass]
    change ((1/3:ℂ)*cubicThetaNinePhase (-omegaE^2*lambdaE*(h*omegaE^(j:ℕ))))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*omegaE)^2*h)=_
    rw [mul_assoc,cubicThetaNinePhase_middle_first hh j]
  have hsecond : F (-(cubicThetaOmegaUnit^2))=
      (1/3:ℂ)*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
    dsimp only [F]
    rw [cubicThetaRamifiedMiddle_second hclass]
    change ((1/3:ℂ)*cubicThetaNinePhase (omegaE*lambdaE*(h*omegaE^(j:ℕ))))*
      cubicThetaNinePhase ((omegaE^(j:ℕ)*(-omegaE^2))^2*h)=_
    rw [mul_assoc,cubicThetaNinePhase_middle_second hh j]
  have hzero (e : Eisensteinˣ) (he : e≠cubicThetaOmegaUnit)
      (he' : e≠-(cubicThetaOmegaUnit^2)) : F e=0 := by
    have hz : cubicThetaRamifiedFactor e 1 (4/3) (lambdaE^2*(h*omegaE^(j:ℕ)))=0 := by
      by_contra hz
      exact (cubicThetaRamifiedMiddleFactor_support e hclass hz).elim he he'
    dsimp only [F]
    rw [hz,zero_mul]
  have hpoint (e : Eisensteinˣ) : F e=
      (if e=cubicThetaOmegaUnit then F cubicThetaOmegaUnit else 0)+
      (if e=-(cubicThetaOmegaUnit^2) then F (-(cubicThetaOmegaUnit^2)) else 0) := by
    by_cases he : e=cubicThetaOmegaUnit
    · subst e
      simp only [ite_true,ite_eq_right cubicThetaOmegaUnit_distinct,add_zero]
    by_cases he' : e=-(cubicThetaOmegaUnit^2)
    · subst e
      simp only [ite_eq_right he,ite_true,zero_add]
    · rw [hzero e he he',ite_eq_right he,ite_eq_right he',zero_add]
  change (∑' e : Eisensteinˣ, F e)=_
  rw [show (∑' e : Eisensteinˣ, F e)=∑' e : Eisensteinˣ,
      ((if e=cubicThetaOmegaUnit then F cubicThetaOmegaUnit else 0)+
       (if e=-(cubicThetaOmegaUnit^2) then F (-(cubicThetaOmegaUnit^2)) else 0)) from
    tsum_congr hpoint]
  rw [Summable.tsum_add Summable.of_finite Summable.of_finite]
  simp only [tsum_ite_eq,hfirst,hsecond]
  ring

end CubicFirstMoment

end

end OAI
