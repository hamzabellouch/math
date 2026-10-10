import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRamifiedModel
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNormalizedSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularFrequency

namespace OAI

/-! The additional integer translation in the full theta group follows
from the proved arithmetic support and the elementary trace pairing. -/
noncomputable section
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaFrequency_integer_phase_cube {n : Eisenstein} (hn : lambdaE^3 ∣ n) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) 1):ℂ)=1 := by
  obtain ⟨k,hk⟩ := hn
  have hf : cubicThetaFrequency n=(k:ℂ)/traceLambda := by
    rw [hk,cubicThetaFrequency]
    push_cast
    rw [lambdaE_coe]
    field_simp [traceLambda_ne_zero]
  have ht : tracePair (cubicThetaFrequency n) 1=tracePair (k:ℂ) (1/traceLambda) := by
    rw [hf]
    unfold tracePair
    congr 1
    apply congrArg Complex.re
    ring
  rw [ht,tracePhase_div_lambda_one]

lemma cubicThetaFrequency_integer_phase_primary {h : Eisenstein} (hh : primary h) :
    (Real.fourierChar (tracePair (cubicThetaFrequency (lambdaE*h)) 1):ℂ)=1 := by
  have hp := cubicThetaNinePhase_three_integer_primary hh (-1)
  rw [cubicThetaNinePhase,residueFourierChar_mk] at hp
  have hlam : traceLambda^2=(-3:ℂ) := by
    have he := congrArg (fun x : Eisenstein => (x:ℂ)) lambdaE_sq
    push_cast at he
    rwa [lambdaE_coe] at he
  have ht : tracePair (cubicThetaFrequency (lambdaE*h)) 1=
      tracePair (((-1:ℤ):Eisenstein)*3*h:ℂ) (1/(((9:Eisenstein):ℂ)*traceLambda)) := by
    unfold tracePair
    congr 1
    apply congrArg Complex.re
    rw [cubicThetaFrequency_div_nine]
    push_cast
    rw [lambdaE_coe]
    rw [show ((9:Eisenstein):ℂ)=(9:ℂ) from rfl]
    field_simp [traceLambda_ne_zero]
    linear_combination (h:ℂ)*hlam
  rw [ht]
  exact hp

lemma cubicThetaFrequency_integer_phase_neg {n : Eisenstein}
    (hn : (Real.fourierChar (tracePair (cubicThetaFrequency n) 1):ℂ)=1) :
    (Real.fourierChar (tracePair (cubicThetaFrequency (-n)) 1):ℂ)=1 := by
  have ht : tracePair (cubicThetaFrequency (-n)) 1= -tracePair (cubicThetaFrequency n) 1 := by
    simp only [cubicThetaFrequency,Subalgebra.coe_neg,neg_div,tracePair,mul_one,Complex.neg_re]
    ring
  rw [ht,AddChar.map_neg_eq_inv,Circle.coe_inv,hn,inv_one]

lemma cubicThetaArithmeticCoefficient_integer_phase {n : Eisenstein}
    (hn : cubicThetaArithmeticCoefficient n≠0) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) 1):ℂ)=1 := by
  have hR : Nonempty (CubicThetaCoordinates n) := by
    by_contra h
    exact hn (by simp only [cubicThetaArithmeticCoefficient,dite_eq_right h])
  let R := Classical.choice hR
  have hcoeff : R.coefficient≠0 := by
    rwa [←cubicThetaArithmeticCoefficient_formula R]
  have hcases : 3≤R.order ∨ R.order=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)= -1) := by
    unfold CubicThetaCoordinates.coefficient at hcoeff
    split_ifs at hcoeff with h0 h1
    · exact Or.inl h0.2
    · by_cases ho : 3≤R.order
      · exact Or.inl ho
      · exact Or.inr ⟨by omega,h1.2⟩
    · exact False.elim (hcoeff rfl)
  rcases hcases with ho | ⟨ho,hu⟩
  · apply cubicThetaFrequency_integer_phase_cube
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le ho
    refine ⟨(R.unit:Eisenstein)*lambdaE^k*(R.squarefreePart*R.cubePart^3),?_⟩
    calc
      n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by rw [hk,pow_add]; ring
  · have hp : primary (R.squarefreePart*R.cubePart^3) :=
      primary_mul R.squarefree_primary (by
        simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
          primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary))
    rw [R.numerator_eq,ho,pow_one]
    rcases hu with hu | hu
    · rw [hu,one_mul]
      exact cubicThetaFrequency_integer_phase_primary hp
    · rw [hu,neg_one_mul,neg_mul]
      exact cubicThetaFrequency_integer_phase_neg (cubicThetaFrequency_integer_phase_primary hp)

lemma cubicThetaArithmeticTerm_integer_periodic (n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm cubicThetaArithmeticCoefficient (z+1) v n=
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v n := by
  by_cases hn : n=0
  · simp [cubicThetaSeriesTerm,hn]
  by_cases ha : cubicThetaArithmeticCoefficient n=0
  · simp [cubicThetaSeriesTerm,ha]
  have ht : tracePair (cubicThetaFrequency n) (z+1)=
      tracePair (cubicThetaFrequency n) z+tracePair (cubicThetaFrequency n) 1 := by
    unfold tracePair
    simp only [mul_add,Complex.add_re,mul_add]
  simp only [cubicThetaSeriesTerm,ite_eq_right hn]
  rw [ht,AddChar.map_add_eq_mul,Circle.coe_mul,
    cubicThetaArithmeticCoefficient_integer_phase ha,mul_one]

theorem cubicThetaArithmetic_integer_periodic (z : ℂ) (v : ℝ) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (z+1,v)=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v) := by
  unfold cubicThetaNonconstant
  exact tsum_congr (fun n => cubicThetaArithmeticTerm_integer_periodic n z v)

theorem cubicThetaNormalizedSeries_integer_periodic {z : ℂ} {v : ℝ} (hv : 0<v) :
    cubicThetaNormalizedSeriesSection.val (⟨(z+1,v),hv⟩ : CubicThetaPoint)=
      cubicThetaNormalizedSeriesSection.val (⟨(z,v),hv⟩ : CubicThetaPoint) := by
  calc
    _ = cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient (z+1,v) :=
      cubicThetaNormalizedSeriesSection_apply (⟨(z+1,v),hv⟩ : CubicThetaPoint)
    _ = cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient (z,v) :=
      congrArg (fun w => cubicThetaSeriesConstant*((v^(2/3:ℝ):ℝ):ℂ)+w)
        (cubicThetaArithmetic_integer_periodic z v)
    _ = _ := (cubicThetaNormalizedSeriesSection_apply (⟨(z,v),hv⟩ : CubicThetaPoint)).symm

end CubicFirstMoment

end

end OAI
