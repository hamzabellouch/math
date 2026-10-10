import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCommonSupport

namespace OAI

/-! A sharp coordinate majorant for the actual three-cusp coefficient.
The ramified shift lowers its amplitude by three, exactly compensating
for the prefactor in the shifted-cusp expansion. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma CubicThetaCoordinates.coefficient_norm_le_amplitude {n : Eisenstein}
    (R : CubicThetaCoordinates n) : ‖R.coefficient‖≤R.amplitude := by
  unfold coefficient
  split_ifs
  · rw [norm_mul,norm_mul,norm_star,cubicThetaUnitPhase_norm,mul_one,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
    exact mul_le_of_le_one_right R.amplitude_nonneg
      (cubicThetaTwistedGauss_norm_le R.squarefree_primary R.squarefree _)
  · rw [norm_mul,norm_star,norm_gauss_of_squarefree R.squarefree_primary R.squarefree,
      mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · simpa only [norm_zero] using R.amplitude_nonneg

lemma cubicThetaArithmetic_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaArithmeticCoefficient ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d) := by
  let R : CubicThetaCoordinates ((e:Eisenstein)*lambdaE^k*(c*d^3)) := {
    unit := e
    order := k
    squarefreePart := c
    cubePart := d
    squarefree_primary := hc
    cube_primary := hd
    squarefree := hs
    numerator_eq := rfl }
  rw [cubicThetaArithmeticCoefficient_formula R]
  exact R.coefficient_norm_le_amplitude

lemma cubicTheta_coordinate_shift_amplitude (k : ℕ) :
    (3:ℝ)*3^(4-(((k+3)/3:ℕ):ℝ))=3^(4-((k/3:ℕ):ℝ)) := by
  have he : (k+3)/3=k/3+1 := by omega
  rw [he]
  push_cast
  rw [show (4-(((k/3:ℕ):ℝ)+1))=(4-((k/3:ℕ):ℝ))-1 by ring]
  rw [Real.rpow_sub (by norm_num : (0:ℝ)<3),Real.rpow_one]
  ring

theorem cubicThetaCommon_coordinate_bound (e : Eisensteinˣ) (k : ℕ)
    {c d : Eisenstein} (hc : primary c) (hd : primary d) (hs : Squarefree c) :
    ‖cubicThetaCommonCuspCoefficient ((e:Eisenstein)*lambdaE^k*(c*d^3))‖≤
      3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d) := by
  let A : ℝ := 3^(4-((k/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)
  have hA : 0≤A := div_nonneg (by positivity)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hb : ‖cubicThetaArithmeticCoefficient (-((e:Eisenstein)*lambdaE^k*(c*d^3)))‖≤A := by
    simpa only [Units.val_neg,neg_mul,A] using
      cubicThetaArithmetic_coordinate_bound (-e) k hc hd hs
  have ht : 3*‖cubicThetaArithmeticCoefficient
      (3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*(c*d^3)))))‖≤A := by
    have he : 3*(lambdaE*(-((e:Eisenstein)*lambdaE^k*(c*d^3))))=
        (e:Eisenstein)*lambdaE^(k+3)*(c*d^3) := by
      have hLam : lambdaE^3= -3*lambdaE := by
        calc
          _ = lambdaE^2*lambdaE := by ring
          _ = _ := by rw [lambdaE_sq]
      rw [pow_add,hLam]
      ring
    rw [he]
    calc
      _ ≤ 3*(3^(4-(((k+3)/3:ℕ):ℝ))/(Real.sqrt (norm c)*norm d)) :=
        mul_le_mul_of_nonneg_left (cubicThetaArithmetic_coordinate_bound e (k+3) hc hd hs)
          (by norm_num)
      _ = A := by rw [←mul_div_assoc,cubicTheta_coordinate_shift_amplitude]
  have hb' (j : ℤ) :
      ‖cubicThetaActualCuspCoefficient j (-((e:Eisenstein)*lambdaE^k*(c*d^3)))‖≤A := by
    unfold cubicThetaActualCuspCoefficient
    split_ifs
    · exact hb
    · unfold cubicThetaShiftedLatticeCoefficient
      split_ifs
      · simpa only [norm_mul,Complex.norm_ofNat] using ht
      · simpa only [norm_zero] using hA
  have hw (j : Fin 3) : ‖omega^j.val‖=1 := by
    have ho : ‖omega‖=1 := by
      have h := cubicTheta_unit_norm
        (Units.mkOfMulEqOne omegaE (omegaE^2) (by rw [mul_comm,←pow_succ,omegaE_cube]))
      exact h
    rw [norm_pow,ho,one_pow]
  unfold cubicThetaCommonCuspCoefficient
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<3)).mpr
  calc
    _ ≤ ∑ j : Fin 3, ‖omega^j.val*
        star (cubicThetaActualCuspCoefficient (j.val:ℤ)
          (-((e:Eisenstein)*lambdaE^k*(c*d^3))))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, A := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_star,hw,one_mul]
      exact hb' _
    _ = A*3 := by simp [mul_comm]

end CubicFirstMoment

end

end OAI
