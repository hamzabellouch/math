import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPeriodicity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryCoefficients

namespace OAI

/-! The additive character that detects the primary cubic theta support.
It is computed from the actual lambda^-4 frequency lattice. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSievePhase (n : Eisenstein) : ℂ :=
  (Real.fourierChar (tracePair (cubicThetaFrequency n) omega):ℂ)

lemma cubicThetaSievePhase_add (m n : Eisenstein) :
    cubicThetaSievePhase (m+n) = cubicThetaSievePhase m*cubicThetaSievePhase n := by
  have he : tracePair (cubicThetaFrequency (m+n)) omega =
      tracePair (cubicThetaFrequency m) omega+tracePair (cubicThetaFrequency n) omega := by
    simp only [tracePair,cubicThetaFrequency,Subalgebra.coe_add,add_div,add_mul,Complex.add_re]
    ring
  simp only [cubicThetaSievePhase,he,AddChar.map_add_eq_mul,Circle.coe_mul]

lemma cubicThetaSievePhase_neg (n : Eisenstein) :
    cubicThetaSievePhase (-n) = star (cubicThetaSievePhase n) := by
  have he : tracePair (cubicThetaFrequency (-n)) omega =
      -tracePair (cubicThetaFrequency n) omega := by
    simp only [tracePair,cubicThetaFrequency,Subalgebra.coe_neg,neg_div,neg_mul,Complex.neg_re]
    ring
  simp only [cubicThetaSievePhase,he,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,Complex.star_def]

lemma cubicThetaSievePhase_ramified (n : Eisenstein) :
    cubicThetaSievePhase (lambdaE^3*n) = 1 := by
  have he : tracePair (cubicThetaFrequency (lambdaE^3*n)) omega =
      tracePair ((n*omegaE:Eisenstein):ℂ) (1/traceLambda) := by
    unfold tracePair cubicThetaFrequency
    congr 2
    push_cast
    rw [lambdaE_coe]
    field_simp
    rfl
  unfold cubicThetaSievePhase
  rw [he,tracePhase_div_lambda_one]

lemma cubicThetaSievePhase_lambda : cubicThetaSievePhase lambdaE = omega^2 := by
  have h4 : traceLambda^4 = 9 := by
    have h2 : traceLambda^2 = -3 := by
      have h := congrArg (fun x : Eisenstein => (x:ℂ)) lambdaE_sq
      push_cast at h
      exact h
    calc
      _ = (traceLambda^2)^2 := by ring
      _ = 9 := by rw [h2]; norm_num
  have ht : tracePair (cubicThetaFrequency lambdaE) omega = -(1/3:ℝ) := by
    unfold tracePair cubicThetaFrequency
    rw [lambdaE_coe,h4,traceLambda_eq]
    norm_num [Complex.mul_re,Complex.mul_im,Complex.div_ofNat_re,Complex.div_ofNat_im,
      omega_re,omega_im]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hw : (Real.fourierChar (1/3:ℝ):ℂ) = omega := by
    rw [Real.fourierChar_apply]
    unfold omega
    congr 1
    push_cast
    ring
  simp only [cubicThetaSievePhase,ht,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,hw]
  exact star_omega

lemma cubicThetaSievePhase_primary {a : Eisenstein} (ha : primary a) :
    cubicThetaSievePhase (lambdaE*a) = omega^2 := by
  obtain ⟨k,hk⟩ := ha
  have hn : lambdaE*a = lambdaE+lambdaE^3*(-k) := by
    linear_combination lambdaE*hk + k*lambdaE*lambdaE_sq
  rw [hn,cubicThetaSievePhase_add,cubicThetaSievePhase_ramified,mul_one,
    cubicThetaSievePhase_lambda]

lemma cubicThetaSievePhase_negative_primary {a : Eisenstein} (ha : primary a) :
    cubicThetaSievePhase (-(lambdaE*a)) = omega := by
  rw [cubicThetaSievePhase_neg,cubicThetaSievePhase_primary ha,star_pow,star_omega]
  calc
    _ = omega^3*omega := by ring
    _ = omega := by rw [omega_cube,one_mul]

/-- Every supported coefficient of ramified order at least three has the
trivial detector phase. -/
lemma cubicThetaSievePhase_high {n : Eisenstein} (R : CubicThetaCoordinates n)
    (hk : 3 ≤ R.order) : cubicThetaSievePhase n = 1 := by
  have hn : n = lambdaE^3*((R.unit:Eisenstein)*lambdaE^(R.order-3)*
      (R.squarefreePart*R.cubePart^3)) := by
    calc
      n = (R.unit:Eisenstein)*lambdaE^R.order*(R.squarefreePart*R.cubePart^3) := R.numerator_eq
      _ = _ := by
        have he : R.order = 3+(R.order-3) := by omega
        conv_lhs => rw [he,pow_add]
        ring
  rw [hn,cubicThetaSievePhase_ramified]

end CubicFirstMoment

end

end OAI
