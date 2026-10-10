import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedTopRow
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPhaseRows

namespace OAI

/-! The selected top-row contribution has the same explicit phase as
the middle-row eigenvector. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaInverseUnitIndex (j : Fin 3) : Fin 3 :=
  if j=0 then 0 else if j=1 then 2 else 1

lemma cubicThetaNegativeInverseUnit_power (j : Fin 3) :
    (((-(cubicThetaOmegaUnit^(j:ℕ))⁻¹):Eisensteinˣ):Eisenstein)=
      -omegaE^(cubicThetaInverseUnitIndex j:ℕ) := by
  fin_cases j
  · norm_num [cubicThetaInverseUnitIndex]
  · norm_num [cubicThetaInverseUnitIndex,cubicThetaOmegaUnit_inverse_value]
  · norm_num [cubicThetaInverseUnitIndex,cubicThetaOmegaUnit_inverse_value]
    change (omegaE^2)^2=omegaE
    rw [←pow_mul,show 2*2=3+1 by omega,pow_add,omegaE_cube,pow_one,one_mul]


lemma cubicThetaTopUnit_congruence (j : Fin 3) :
    (3:Eisenstein)∣(omegaE^(j:ℕ))^2+2+lambdaE*(cubicThetaInverseUnitIndex j:ℕ) := by
  fin_cases j
  · refine ⟨1,?_⟩
    norm_num [cubicThetaInverseUnitIndex]
  · refine ⟨1+omegaE,?_⟩
    norm_num [cubicThetaInverseUnitIndex]
    dsimp only [lambdaE]
    linear_combination omegaE_quadratic
  · refine ⟨1+omegaE,?_⟩
    norm_num [cubicThetaInverseUnitIndex]
    dsimp only [lambdaE]
    linear_combination (omegaE^2-omegaE)*omegaE_quadratic

theorem cubicThetaRamifiedTop_negative_inverse {h : Eisenstein} (hh : primary h) (j : Fin 3) :
    cubicThetaRamifiedFactor (-(cubicThetaOmegaUnit^(j:ℕ))⁻¹) 2 (4/3)
      (lambdaE^2*(h*omegaE^(j:ℕ)))=
        ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h) := by
  let d : Eisensteinˣ := cubicThetaOmegaUnit^(j:ℕ)
  have hd : (d:Eisenstein)=omegaE^(j:ℕ) := by
    simp only [d,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne]
  have hiU : (-(d⁻¹))⁻¹=-d := by rw [inv_neg,inv_inv]
  have hi := congrArg (fun u : Eisensteinˣ => (u:Eisenstein)) hiU
  simp only [Units.val_neg] at hi
  have hc : (3:Eisenstein)∣(omegaE^(j:ℕ))^2*h+2+lambdaE*(cubicThetaInverseUnitIndex j:ℕ) := by
    have hm := dvd_mul_of_dvd_right hh ((omegaE^(j:ℕ))^2)
    convert dvd_add hm (cubicThetaTopUnit_congruence j) using 1
    ring
  rw [cubicThetaRamifiedTopFactor_eq (-(d⁻¹)) (cubicThetaInverseUnitIndex j)
    (Or.inr (cubicThetaNegativeInverseUnit_power j)) (h*omegaE^(j:ℕ)),hi,hd,neg_neg]
  have he : omegaE^(j:ℕ)*(h*omegaE^(j:ℕ))=(omegaE^(j:ℕ))^2*h := by ring
  rw [he,ite_eq_left hc]

end CubicFirstMoment

end

end OAI
