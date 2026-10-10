import OAI.NumberTheory.CubicMoment.Estimates.OuterDyadicSum
import OAI.NumberTheory.CubicMoment.Estimates.OuterPoissonAnnulus

namespace OAI

/-! Numerical summation of the common-factor outer sieve at the exact
Poisson frequency scale. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma outer_scaled_envelope {J T ε : ℝ} (hJ : 0 < J) (hT : 0 ≤ T) :
    (4*J*T)^ε*(2*J+(2*J*T)^(2/3:ℝ)+(2*J)^(1/3:ℝ)*T) ≤
      2*(4*T)^ε*J^ε*(J+(J*T)^(2/3:ℝ)+J^(1/3:ℝ)*T) := by
  have h2 : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (2/3:ℝ) ≤ 1)
  have h1 : (2:ℝ)^(1/3:ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (1/3:ℝ) ≤ 1)
  have heq : (4*J*T)^ε = (4*T)^ε*J^ε := by
    rw [show 4*J*T = (4*T)*J by ring,Real.mul_rpow (by positivity) hJ.le]
  rw [heq,show 2*J*T = 2*(J*T) by ring,
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hJ.le hT),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le]
  have hp : 2*J+2^(2/3:ℝ)*(J*T)^(2/3:ℝ)+2^(1/3:ℝ)*J^(1/3:ℝ)*T ≤
      2*(J+(J*T)^(2/3:ℝ)+J^(1/3:ℝ)*T) := by
    have hp2 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (mul_nonneg hJ.le hT) (2/3))
    have hp1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hJ.le (1/3))) hT
    linarith
  exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq (by ring)

lemma finite_outer_poisson_sum (I : Finset ℕ) (F : ℕ → ℂ)
    {C Z N T ε : ℝ} (hC : 0 ≤ C) (hZ : 0 < Z) (hN : 0 < N) (hT : 0 ≤ T)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hF : ∀ j ∈ I, (1+Z*2^j/(27*N^2))^3*‖F j‖ ≤
      C*(Z/N)*(4*2^j*T)^ε*
        (2*2^j+(2*2^j*T)^(2/3:ℝ)+(2*2^j)^(1/3:ℝ)*T)) :
    ‖∑ j ∈ I, F j‖ ≤
      (2*C*(Z/N)*(4*T)^ε)*outerDyadicBound ε T (Z/(27*N^2)) := by
  let t := Z/(27*N^2)
  have ht : 0 < t := by dsimp [t]; positivity
  let K := 2*C*(Z/N)*(4*T)^ε
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hj (j : ℕ) (hj : j ∈ I) : ‖F j‖ ≤
      K*(((2:ℝ)^j)^ε*((2:ℝ)^j+((2:ℝ)^j*T)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*T)/
        (1+t*2^j)^3) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < (1+t*2^j)^3)).mpr
    have hstart := hF j hj
    rw [mul_assoc (C*(Z/N))] at hstart
    have hh := hstart.trans
      (mul_le_mul_of_nonneg_left (outer_scaled_envelope (ε := ε) (by positivity : (0:ℝ) < 2^j) hT)
        (by positivity : 0 ≤ C*(Z/N)))
    convert hh using 1 <;> dsimp [t,K] <;> ring
  calc
    _ ≤ ∑ j ∈ I, ‖F j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ I, K*(((2:ℝ)^j)^ε*((2:ℝ)^j+
        ((2:ℝ)^j*T)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*T)/(1+t*2^j)^3) :=
      Finset.sum_le_sum hj
    _ = K*∑ j ∈ I, ((2:ℝ)^j)^ε*((2:ℝ)^j+
        ((2:ℝ)^j*T)^(2/3:ℝ)+((2:ℝ)^j)^(1/3:ℝ)*T)/(1+t*2^j)^3 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_outer_dyadic_envelope I hε hε1 hT ht) hK

end CubicFirstMoment

end

end OAI
