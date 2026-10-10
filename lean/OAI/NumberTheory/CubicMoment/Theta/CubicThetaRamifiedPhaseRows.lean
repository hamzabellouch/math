import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPhaseTransport

namespace OAI

/-! Exact phase of each of the two nonzero middle ramified rows. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaOmegaUnit_inverse_value :
    (((cubicThetaOmegaUnit)⁻¹:Eisensteinˣ):Eisenstein)=omegaE^2 := rfl

lemma cubicThetaOmegaUnit_square_inverse_value :
    (((cubicThetaOmegaUnit^2)⁻¹:Eisensteinˣ):Eisenstein)=omegaE := by
  rw [←inv_pow,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit_inverse_value,←pow_mul,
    show 2*2=3+1 by omega,pow_add,omegaE_cube,pow_one,one_mul]

lemma cubicThetaOmegaUnit_distinct : cubicThetaOmegaUnit≠-(cubicThetaOmegaUnit^2) := by
  intro he
  have hv : omegaE=-(omegaE^2) := by
    simpa only [Units.val_neg,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using
      congrArg (fun e : Eisensteinˣ => (e:Eisenstein)) he
  have hz : (1:Eisenstein)=0 := by linear_combination omegaE_quadratic-hv
  exact one_ne_zero hz

lemma cubicThetaLambda_dvd_three : lambdaE∣(3:Eisenstein) := by
  refine ⟨-lambdaE,?_⟩
  rw [mul_neg,←pow_two,lambdaE_sq]
  ring

lemma cubicThetaLambda_dvd_primary_sub_one {h : Eisenstein} (hh : primary h) :
    lambdaE∣h-1 := cubicThetaLambda_dvd_three.trans hh

lemma cubicThetaLambda_dvd_primary_omega_sub_one {h : Eisenstein} (hh : primary h) (k : ℕ) :
    lambdaE∣h*omegaE^k-1 := by
  convert dvd_add (dvd_mul_of_dvd_left (cubicThetaLambda_dvd_primary_sub_one hh) (omegaE^k))
    (cubicThetaLambda_dvd_omega_pow_sub_one k) using 1
  ring

lemma cubicThetaRamifiedMiddle_first {h : Eisenstein} (hh : lambdaE∣h-1) :
    cubicThetaRamifiedFactor cubicThetaOmegaUnit 1 (4/3) (lambdaE^2*h)=
      (1/3:ℂ)*cubicThetaNinePhase (-omegaE^2*lambdaE*h) := by
  have ht : lambdaE∣omegaE^2*h-1 := by
    convert dvd_add (dvd_mul_of_dvd_left (cubicThetaLambda_dvd_omega_pow_sub_one 2) h) hh using 1
    ring
  have hc : (3:Eisenstein)∣lambdaE*(-omegaE^2*h+1) :=
    (cubicThetaThree_dvd_lambda_mul _).mpr (by
      convert dvd_neg.mpr ht using 1
      ring)
  rw [cubicThetaRamifiedMiddleFactor_eq cubicThetaOmegaUnit (1:Fin 3)
    (Or.inl (by norm_num [cubicThetaOmegaUnit])) h,cubicThetaOmegaUnit_inverse_value]
  norm_num only [Fin.val_one,Nat.cast_one]
  rw [ite_eq_left hc]
  congr 2
  ring_nf

lemma cubicThetaRamifiedMiddle_second {h : Eisenstein} (hh : lambdaE∣h-1) :
    cubicThetaRamifiedFactor (-(cubicThetaOmegaUnit^2)) 1 (4/3) (lambdaE^2*h)=
      (1/3:ℂ)*cubicThetaNinePhase (omegaE*lambdaE*h) := by
  have hi : (((-(cubicThetaOmegaUnit^2))⁻¹:Eisensteinˣ):Eisenstein)=-omegaE := by
    rw [inv_neg,Units.val_neg,cubicThetaOmegaUnit_square_inverse_value]
  have ht : lambdaE∣omegaE*h-1 := by
    convert dvd_add (dvd_mul_of_dvd_left (cubicThetaLambda_dvd_omega_pow_sub_one 1) h) hh using 1
    ring
  have hc : (3:Eisenstein)∣lambdaE*(omegaE*h+2) :=
    (cubicThetaThree_dvd_lambda_mul _).mpr (by
      convert dvd_add ht cubicThetaLambda_dvd_three using 1
      ring)
  rw [cubicThetaRamifiedMiddleFactor_eq (-(cubicThetaOmegaUnit^2)) (2:Fin 3)
    (Or.inr (by norm_num [Units.val_pow_eq_pow_val,cubicThetaOmegaUnit])) h,hi]
  norm_num only [Fin.val_two,Nat.cast_ofNat,neg_neg]
  rw [ite_eq_left hc]
  congr 2
  ring_nf

end CubicFirstMoment

end

end OAI
