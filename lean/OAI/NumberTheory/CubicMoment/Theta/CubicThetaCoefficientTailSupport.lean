import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAmplitudeTail
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryCoefficients
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEven

namespace OAI

/-! Exact support and coefficient bounds for the arithmetic remainder after
removing the two leading Fourier frequencies. -/
noncomputable section
namespace CubicFirstMoment

lemma cubic_primary_norm_ge_four {m : Eisenstein} (hm : primary m) (hne : m≠1) :
    4≤norm m := by
  obtain ⟨w,hw⟩ := hm
  have hw0 : w≠0 := by intro h; rw [h,mul_zero,sub_eq_zero] at hw; exact hne hw
  have hw1 : 1≤‖(w:ℂ)‖ := by
    have h := one_le_norm hw0
    rw [norm,Complex.normSq_eq_norm_sq] at h
    nlinarith [_root_.norm_nonneg (w:ℂ)]
  have h3 : ‖(m:ℂ)-1‖=3*‖(w:ℂ)‖ := by
    have h := congrArg (fun z : Eisenstein => (z:ℂ)) hw
    simp only [Subalgebra.coe_sub,Subalgebra.coe_one,Subalgebra.coe_mul] at h
    change (m:ℂ)-1=(3:ℂ)*(w:ℂ) at h
    rw [h,norm_mul]
    norm_num
  have htri := norm_sub_le (m:ℂ) 1
  norm_num only [norm_one] at htri
  have hm2 : 2≤‖(m:ℂ)‖ := by linarith
  rw [norm,Complex.normSq_eq_norm_sq]
  nlinarith

lemma CubicThetaCoordinates.coefficient_norm_le_amplitude {n : Eisenstein}
    (R : CubicThetaCoordinates n) : ‖R.coefficient‖≤R.amplitude := by
  rw [R.coefficient_norm]
  split_ifs <;> first | exact le_rfl | exact R.amplitude_nonneg

lemma CubicThetaCoordinates.amplitude_order_one_bound {n : Eisenstein}
    (R : CubicThetaCoordinates n) (hk : R.order=1)
    (hm : R.squarefreePart*R.cubePart^3≠1) : R.amplitude≤81/2 := by
  have hden : 2≤Real.sqrt (norm R.squarefreePart)*norm R.cubePart := by
    have hc1 := one_le_norm (primary_ne_zero R.squarefree_primary)
    have hd1 := one_le_norm (primary_ne_zero R.cube_primary)
    have hs1 : 1≤Real.sqrt (norm R.squarefreePart) := by simpa using Real.sqrt_le_sqrt hc1
    by_cases hc : R.squarefreePart=1
    · have hd : R.cubePart≠1 := by intro h; apply hm; simp [hc,h]
      have hd4 := cubic_primary_norm_ge_four R.cube_primary hd
      nlinarith
    · have hc4 := cubic_primary_norm_ge_four R.squarefree_primary hc
      have hs2 : 2≤Real.sqrt (norm R.squarefreePart) := by
        convert Real.sqrt_le_sqrt hc4 using 1
        norm_num
      nlinarith
  have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤81) (by norm_num : (0:ℝ)<2) hden
  convert h using 1
  norm_num [CubicThetaCoordinates.amplitude,hk]

lemma cubicThetaArithmetic_remainder_support {n : Eisenstein}
    (hp : n≠lambdaE) (hm : n≠ -lambdaE) (hc : cubicThetaArithmeticCoefficient n≠0) :
    (∃ m : Eisenstein,primary m ∧ m≠1 ∧ (n=lambdaE*m ∨ n= -lambdaE*m) ∧
      ‖cubicThetaArithmeticCoefficient n‖≤81/2) ∨
    (∃ m : Eisenstein,m≠0 ∧ n=lambdaE^3*m ∧ ‖cubicThetaArithmeticCoefficient n‖≤27) := by
  classical
  have hR : Nonempty (CubicThetaCoordinates n) := by
    by_contra h
    exact hc (by simp [cubicThetaArithmeticCoefficient,h])
  let R := Classical.choice hR
  have hcR : R.coefficient≠0 := by rwa [cubicThetaArithmeticCoefficient_formula R] at hc
  rcases R.nonzero_order_cases hcR with ⟨hk,hu⟩ | hk
  · left
    let m := R.squarefreePart*R.cubePart^3
    have hmp : primary m := primary_mul R.squarefree_primary (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul R.cube_primary (primary_mul R.cube_primary R.cube_primary))
    have he : n=lambdaE*m ∨ n= -lambdaE*m := by
      rcases hu with hu | hu
      · left; rw [R.numerator_eq,hk,pow_one,hu,one_mul]
      · right; rw [R.numerator_eq,hk,pow_one,hu]; ring
    have hm1 : m≠1 := by
      intro h
      rcases he with he | he
      · exact hp (by simpa only [h,mul_one] using he)
      · exact hm (by simpa only [h,mul_one] using he)
    refine ⟨m,hmp,hm1,he,?_⟩
    rw [cubicThetaArithmeticCoefficient_formula R]
    exact R.coefficient_norm_le_amplitude.trans (R.amplitude_order_one_bound hk hm1)
  · right
    let m := (R.unit:Eisenstein)*lambdaE^(R.order-3)*(R.squarefreePart*R.cubePart^3)
    have he : n=lambdaE^3*m := by
      rw [R.numerator_eq,show R.order=3+(R.order-3) by omega,pow_add]
      dsimp [m]
      ring
    have hm0 : m≠0 := by intro h; exact R.ne_zero (by rw [he,h,mul_zero])
    refine ⟨m,hm0,he,?_⟩
    rw [cubicThetaArithmeticCoefficient_formula R]
    exact R.coefficient_norm_le_amplitude.trans (R.amplitude_high_order_bound hk)

end CubicFirstMoment

end

end OAI
