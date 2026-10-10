import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedUnitOperator

namespace OAI

/-! Explicit solution of the actual ramified residue system. The phase
is obtained from the finite rows and uniqueness from their strict contraction. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

private instance : Finite Eisensteinˣ :=
  Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)

def cubicThetaRamifiedPhaseCandidate (h : Eisenstein) (d : Eisensteinˣ) : ℂ :=
  (3:ℂ)^(-(1/3:ℂ))*(cubicThetaNinePhase ((d:Eisenstein)^2*h)*
    cubicThetaArithmeticFourierResidue h (4/3))

lemma cubicThetaRamifiedPhaseCandidate_neg (h : Eisenstein) (d : Eisensteinˣ) :
    cubicThetaRamifiedPhaseCandidate h (-d)=cubicThetaRamifiedPhaseCandidate h d := by
  unfold cubicThetaRamifiedPhaseCandidate
  rw [Units.val_neg,neg_sq]

lemma cubicThetaRamifiedPhaseCandidate_system {h : Eisenstein} (hh : primary h)
    (d : Eisensteinˣ) :
    cubicThetaRamifiedPhaseCandidate h d=
      cubicThetaRamifiedUnitOperator 1 h (cubicThetaRamifiedPhaseCandidate h) d+
      cubicThetaRamifiedUnitOperator 2 h
        (fun e => cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3)) d := by
  have hpos (j : Fin 3) : cubicThetaRamifiedPhaseCandidate h (cubicThetaOmegaUnit^(j:ℕ))=
      cubicThetaRamifiedUnitOperator 1 h (cubicThetaRamifiedPhaseCandidate h)
        (cubicThetaOmegaUnit^(j:ℕ))+
      cubicThetaRamifiedUnitOperator 2 h
        (fun e => cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3))
        (cubicThetaOmegaUnit^(j:ℕ)) := by
    let u : Eisensteinˣ := cubicThetaOmegaUnit^(j:ℕ)
    have hu : (u:Eisenstein)=omegaE^(j:ℕ) := by
      simp only [u,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne]
    have hm : cubicThetaRamifiedUnitOperator 1 h
        (fun e => cubicThetaNinePhase ((e:Eisenstein)^2*h)) u=
        (2/3:ℂ)*cubicThetaNinePhase ((u:Eisenstein)^2*h) := by
      simpa only [cubicThetaRamifiedUnitOperator,Units.val_mul,hu] using
        cubicThetaRamifiedMiddle_phase_eigen hh j
    have hb : cubicThetaRamifiedUnitOperator 2 h
        (fun e => cubicThetaArithmeticFourierResidue (h*(e:Eisenstein)) (4/3)) u=
        ((1/3:ℂ)*(3:ℂ)^(-(1/3:ℂ)))*cubicThetaNinePhase ((u:Eisenstein)^2*h)*
          cubicThetaArithmeticFourierResidue h (4/3) := by
      simpa only [cubicThetaRamifiedUnitOperator,Units.val_mul,hu,mul_assoc] using
        cubicThetaRamifiedForcing_phase hh j
    change cubicThetaRamifiedPhaseCandidate h u= _
    unfold cubicThetaRamifiedPhaseCandidate
    rw [cubicThetaRamifiedUnitOperator_mul_left,cubicThetaRamifiedUnitOperator_mul_right,hm,hb]
    ring
  obtain ⟨j,hj | hj⟩ := cubicThetaUnit_signed_power d
  · have he : d=cubicThetaOmegaUnit^(j:ℕ) := by
      apply Units.ext
      simpa only [Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using hj
    rw [he]
    exact hpos j
  · have he : d=-(cubicThetaOmegaUnit^(j:ℕ)) := by
      apply Units.ext
      simpa only [Units.val_neg,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using hj
    rw [he,cubicThetaRamifiedPhaseCandidate_neg,cubicThetaRamifiedUnitOperator_neg,
      cubicThetaRamifiedUnitOperator_neg]
    exact hpos j

theorem cubicThetaArithmeticFourierResidue_lambda_square_unit {h : Eisenstein}
    (hh : primary h) (d : Eisensteinˣ) :
    cubicThetaArithmeticFourierResidue (lambdaE^2*(h*(d:Eisenstein))) (4/3)=
      (3:ℂ)^(-(1/3:ℂ))*(cubicThetaNinePhase ((d:Eisenstein)^2*h)*
        cubicThetaArithmeticFourierResidue h (4/3)) := by
  let f (e : Eisensteinˣ) := cubicThetaArithmeticFourierResidue
    (lambdaE^2*(h*(e:Eisenstein))) (4/3)
  let b (e : Eisensteinˣ) := cubicThetaRamifiedUnitOperator 2 h
    (fun u => cubicThetaArithmeticFourierResidue (h*(u:Eisenstein)) (4/3)) e
  have hf (e : Eisensteinˣ) : f e=(∑' u : Eisensteinˣ,
      cubicThetaRamifiedFactor u 1 (4/3) (lambdaE^2*(h*(e:Eisenstein)))*f (e*u))+b e := by
    have hc : ¬lambdaE∣h*(e:Eisenstein) := by
      intro hd
      rcases lambdaE_prime.dvd_mul.mp hd with hd | hd
      · exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hh).isRelPrime hd dvd_rfl)
      · exact lambdaE_prime.not_isUnit (isUnit_of_dvd_unit hd e.isUnit)
    dsimp only [f,b,cubicThetaRamifiedUnitOperator]
    rw [cubicThetaArithmeticFourierResidue_lambda_square_system hc,
      ←Summable.tsum_add Summable.of_finite Summable.of_finite]
    apply tsum_congr
    intro u
    rw [Units.val_mul,mul_assoc]
  have hg (e : Eisensteinˣ) : cubicThetaRamifiedPhaseCandidate h e=(∑' u : Eisensteinˣ,
      cubicThetaRamifiedFactor u 1 (4/3) (lambdaE^2*(h*(e:Eisenstein)))*
        cubicThetaRamifiedPhaseCandidate h (e*u))+b e :=
    cubicThetaRamifiedPhaseCandidate_system hh e
  have he := cubicThetaRamifiedUnitSystem_unique (cubicThetaLambda_dvd_primary_sub_one hh)
    b f (cubicThetaRamifiedPhaseCandidate h) hf hg
  exact congrFun he d

theorem cubicThetaArithmeticFourierResidue_lambda_square {h : Eisenstein} (hh : primary h) :
    cubicThetaArithmeticFourierResidue (lambdaE^2*h) (4/3)=
      (3:ℂ)^(-(1/3:ℂ))*(cubicThetaNinePhase h*cubicThetaArithmeticFourierResidue h (4/3)) := by
  simpa only [Units.val_one,one_pow,mul_one,one_mul] using
    cubicThetaArithmeticFourierResidue_lambda_square_unit hh (1:Eisensteinˣ)

end CubicFirstMoment

end

end OAI
