import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNinePhaseSymbol
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedPhaseRows

namespace OAI

/-! Exact matching of the unit phase and supplementary symbol in the
ramified arithmetic theta coefficient. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaNinePhase_congr {a b : Eisenstein} (hab : (9:Eisenstein)∣a-b) :
    cubicThetaNinePhase a=cubicThetaNinePhase b :=
  congrArg (residueFourierChar 9 (by norm_num)) (residue_eq_of_dvd_sub hab)

lemma cubicThetaNinePhase_omega :
    cubicThetaNinePhase omegaE=(Real.fourierChar (1/9):ℂ) := by
  have he : ofCoords 0 1=omegaE := by
    apply Subtype.ext
    simp [ofCoords_coe,omegaE]
  simpa only [he,Int.cast_one] using cubicThetaNinePhase_coordinates 0 1

lemma cubicThetaNinePhase_omega_square :
    cubicThetaNinePhase (omegaE^2)=(Real.fourierChar (-1/9):ℂ) := by
  have he : ofCoords (-1) (-1)=omegaE^2 := by
    have h : ofCoords (-1) (-1)= -1-omegaE := by
      apply Subtype.ext
      simp [ofCoords_coe,omegaE,sub_eq_add_neg]
    rw [h]
    linear_combination -omegaE_quadratic
  simpa only [he,Int.cast_neg,Int.cast_one] using cubicThetaNinePhase_coordinates (-1) (-1)

lemma cubicThetaUnitPhase_neg (e : Eisensteinˣ) :
    cubicThetaUnitPhase (-e)=cubicThetaUnitPhase e := by
  have hneg : (-(e:Eisenstein))^4=(e:Eisenstein)^4 := by ring
  simp only [cubicThetaUnitPhase,Units.val_neg,hneg]

lemma cubicThetaUnitPhase_omega_power (j : Fin 3) :
    cubicThetaUnitPhase (cubicThetaOmegaUnit^(j:ℕ))=
      cubicThetaNinePhase ((omegaE^(j:ℕ))^2) := by
  have h1 := omegaE_primitive.ne_one (by norm_num : 1<3)
  have h2 := omegaE_primitive.pow_ne_one_of_pos_of_lt (by norm_num : (2:ℕ)≠0)
    (by norm_num : (2:ℕ)<3)
  have h4 : omegaE^4=omegaE := by rw [show 4=3+1 by omega,pow_add,omegaE_cube]; simp
  have h8 : omegaE^8=omegaE^2 := by rw [show 8=3*2+2 by omega,pow_add,pow_mul,omegaE_cube]; simp
  have h21 : omegaE^2≠omegaE := by
    intro he
    have hz : omegaE*(omegaE-1)=0 := by linear_combination he
    rcases mul_eq_zero.mp hz with hz|hz
    · exact (omegaE_primitive.ne_zero (by norm_num)) hz
    · exact h1 (sub_eq_zero.mp hz)
  fin_cases j
  · simp [cubicThetaUnitPhase,cubicThetaOmegaUnit,cubicThetaNinePhase_one]
  · simp only [pow_one,cubicThetaUnitPhase,cubicThetaOmegaUnit,
      Units.val_mkOfMulEqOne,h4,h1,ite_false,ite_true]
    exact cubicThetaNinePhase_omega_square.symm
  · simp only [Units.val_pow_eq_pow_val,cubicThetaUnitPhase,
      cubicThetaOmegaUnit,Units.val_mkOfMulEqOne,←pow_mul]
    norm_num only [Nat.reduceMul]
    rw [h8,h4,ite_eq_right h2,ite_eq_right h21]
    exact cubicThetaNinePhase_omega.symm

theorem cubicThetaUnitPhase_eq (e : Eisensteinˣ) :
    cubicThetaUnitPhase e=cubicThetaNinePhase ((e:Eisenstein)^2) := by
  obtain ⟨j,hj|hj⟩ := cubicThetaUnit_signed_power e
  · have he : e=cubicThetaOmegaUnit^(j:ℕ) := Units.ext (by
      simpa only [Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using hj)
    simpa only [he,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,Units.val_mkOfMulEqOne] using
      cubicThetaUnitPhase_omega_power j
  · have he : e=-(cubicThetaOmegaUnit^(j:ℕ)) := Units.ext (by
      simpa only [Units.val_neg,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,
        Units.val_mkOfMulEqOne] using hj)
    rw [he,cubicThetaUnitPhase_neg]
    simpa only [Units.val_neg,Units.val_pow_eq_pow_val,cubicThetaOmegaUnit,
      Units.val_mkOfMulEqOne,neg_sq] using cubicThetaUnitPhase_omega_power j

lemma cubicThetaUnit_square_congruence (j : Fin 3) :
    (3:Eisenstein)∣(omegaE^(j:ℕ))^2-1-lambdaE*(4*(j:ℕ)) := by
  fin_cases j
  · norm_num
  · refine ⟨-2-3*omegaE,?_⟩
    norm_num only [Fin.val_one,pow_one,Nat.cast_one,mul_one]
    dsimp only [lambdaE]
    linear_combination omegaE_quadratic
  · refine ⟨-3-5*omegaE,?_⟩
    norm_num only [Fin.val_two,Nat.cast_ofNat,←pow_mul,Nat.reduceMul]
    dsimp only [lambdaE]
    linear_combination (omegaE^2-omegaE)*omegaE_quadratic

theorem cubicThetaNinePhase_unit_primary {h : Eisenstein} (hh : primary h)
    (e : Eisensteinˣ) :
    cubicThetaNinePhase ((e:Eisenstein)^2*h)=
      cubicThetaUnitPhase e*cubicSymbol h ((e:Eisenstein)^4*lambdaE^2) := by
  have hsub : cubicThetaNinePhase (h-1)=cubicThetaNinePhase h := by
    calc
      _ = cubicThetaNinePhase (h-1)*cubicThetaNinePhase 1 := by rw [cubicThetaNinePhase_one,mul_one]
      _ = _ := by rw [←cubicThetaNinePhase_add]; congr 1; ring
  have H (j : Fin 3) : cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h)=
      cubicThetaNinePhase ((omegaE^(j:ℕ))^2)*
        cubicSymbol h ((omegaE^(j:ℕ))^4*lambdaE^2) := by
    rw [cubicSymbol_mul_upper hh,←cubicThetaNinePhase_primary hh,←hsub,
      show (omegaE^(j:ℕ))^4=omegaE^(4*(j:ℕ)) by rw [←pow_mul]; congr 1; omega,
      cubicSymbol_pow_upper hh,cubicThetaUnitCharacter_power hh]
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
    change cubicThetaNinePhase ((omegaE^(j:ℕ))^2*h)=
      cubicThetaNinePhase ((omegaE^(j:ℕ))^2)*
        (cubicThetaNinePhase (lambdaE*(4*(j:ℕ))*(h-1))*cubicThetaNinePhase (h-1))
    rw [←cubicThetaNinePhase_add,←cubicThetaNinePhase_add]
    apply cubicThetaNinePhase_congr
    obtain ⟨t,ht⟩ := hh
    obtain ⟨b,hb⟩ := cubicThetaUnit_square_congruence j
    refine ⟨b*t,?_⟩
    calc
      _ = ((omegaE^(j:ℕ))^2-1-lambdaE*(4*(j:ℕ)))*(h-1) := by ring
      _ = _ := by rw [hb,ht]; ring
  rw [cubicThetaUnitPhase_eq]
  obtain ⟨j,hj|hj⟩ := cubicThetaUnit_signed_power e
  · rw [hj]; exact H j
  · have hneg : (-(omegaE^(j:ℕ)))^4=(omegaE^(j:ℕ))^4 := by ring
    simpa only [hj,neg_sq,hneg] using H j

end CubicFirstMoment

end

end OAI
