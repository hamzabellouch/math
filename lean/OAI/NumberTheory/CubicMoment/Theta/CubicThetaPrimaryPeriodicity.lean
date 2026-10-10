import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPeriodicity

namespace OAI

/-! The base theta series has the smaller period lattice 3 Z[omega].
This follows from its actual ramified support, and supplies the upper
unipotent stabilizer for the principal level-three group. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticCoefficient_lambda_dvd {n : Eisenstein}
    (hn : cubicThetaArithmeticCoefficient n ≠ 0) : lambdaE ∣ n := by
  unfold cubicThetaArithmeticCoefficient at hn
  split_ifs at hn with h
  · let R := Classical.choice h
    have hR : R.coefficient ≠ 0 := hn
    have ho : 0 < R.order := by
      unfold CubicThetaCoordinates.coefficient at hR
      split_ifs at hR with h0 h1
      · omega
      · have hm := h1.1
        omega
      · exact False.elim (hR rfl)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ho)
    refine ⟨(R.unit:Eisenstein)*lambdaE^k*(R.squarefreePart*R.cubePart^3),?_⟩
    calc
      n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by rw [hk,pow_succ]; ring
  · exact False.elim (hn rfl)

lemma cubicThetaFrequency_three_phase {n : Eisenstein} (hn : lambdaE ∣ n) (m : Eisenstein) :
    (Real.fourierChar (tracePair (cubicThetaFrequency n) ((3*m:Eisenstein):ℂ)):ℂ) = 1 := by
  obtain ⟨k,hk⟩ := hn
  have hlam : traceLambda^2 = (-3:ℂ) := by
    have he := congrArg (fun x : Eisenstein => (x:ℂ)) lambdaE_sq
    push_cast at he
    rwa [lambdaE_coe] at he
  have he : tracePair (cubicThetaFrequency n) ((3*m:Eisenstein):ℂ) =
      tracePair ((-k*m:Eisenstein):ℂ) (1/traceLambda) := by
    unfold tracePair cubicThetaFrequency
    congr 2
    rw [hk]
    push_cast
    rw [lambdaE_coe]
    change traceLambda*(k:ℂ)/traceLambda^4*(3*(m:ℂ)) =
      (-(k:ℂ)*(m:ℂ))*(1/traceLambda)
    field_simp [traceLambda_ne_zero]
    linear_combination (k:ℂ)*(m:ℂ)*hlam
  rw [he,tracePhase_div_lambda_one]

lemma cubicThetaArithmeticTerm_three_periodic (m n : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaSeriesTerm cubicThetaArithmeticCoefficient (z+((3*m:Eisenstein):ℂ)) v n =
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient z v n := by
  by_cases hn : n = 0
  · simp [cubicThetaSeriesTerm,hn]
  by_cases ha : cubicThetaArithmeticCoefficient n = 0
  · simp [cubicThetaSeriesTerm,ha]
  have he : tracePair (cubicThetaFrequency n) (z+((3*m:Eisenstein):ℂ)) =
      tracePair (cubicThetaFrequency n) z+
        tracePair (cubicThetaFrequency n) ((3*m:Eisenstein):ℂ) := by
    unfold tracePair
    simp only [mul_add,Complex.add_re,mul_add]
  simp only [cubicThetaSeriesTerm,hn,ite_false]
  rw [he,AddChar.map_add_eq_mul,Circle.coe_mul,
    cubicThetaFrequency_three_phase (cubicThetaArithmeticCoefficient_lambda_dvd ha),mul_one]

theorem cubicThetaFunction_three_periodic (m : Eisenstein) (z : ℂ) (v : ℝ) :
    cubicThetaFunction (z+((3*m:Eisenstein):ℂ),v) = cubicThetaFunction (z,v) := by
  unfold cubicThetaFunction cubicThetaAuxiliarySeries
  rw [cubicThetaCuspCoefficient_zero]
  congr 1
  unfold cubicThetaNonconstant
  apply tsum_congr
  intro n
  exact cubicThetaArithmeticTerm_three_periodic m n z v

end CubicFirstMoment

end

end OAI
