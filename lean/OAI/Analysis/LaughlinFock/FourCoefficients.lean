import Mathlib
import OAI.Analysis.LaughlinFock.OscillatorLimit

namespace OAI

/-! Four Coefficients. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators
open Filter Topology

 
theorem coupledCoefficient_left_support {n m z : ℕ} (hz : z ≤ n)
    (k p : ℕ) (hp : n < p) : coupledCoefficient n m z k p = 0 := by
  induction k generalizing p with
  | zero => exact highestCoefficient_zero _ _ _ _ (by omega)
  | succ k ih =>
    rw [coupledCoefficient, ih p hp]
    simp only [mul_zero, add_zero]
    by_cases he : p = n+1
    · rw [he]
      have he' : (n : ℝ)+1-(n+1 : ℕ) = 0 := by push_cast; ring
      simp only [he', mul_zero, Real.sqrt_zero, zero_mul]
      split_ifs <;> simp
    · rw [ite_eq_right (by omega : p ≠ 0), ih (p-1) (by omega)]
      simp

 

theorem coupledCoefficient_right_support {n m z : ℕ} (hz : z ≤ m)
    (k p : ℕ) (hp : m+p < z+k) : coupledCoefficient n m z k p = 0 := by
  induction k generalizing p with
  | zero => omega
  | succ k ih =>
    rw [coupledCoefficient]
    have hfirst : (if p = 0 then 0 else
        Real.sqrt ((p : ℝ)*((n : ℝ)+1-p)) * coupledCoefficient n m z k (p-1)) = 0 := by
      split_ifs with hp0
      · rfl
      · rw [ih (p-1) (by omega), mul_zero]
    rw [hfirst, zero_add]
    by_cases he : m+p = z+k
    · have he' : (m : ℝ)+p-z-k = 0 := by exact_mod_cast sub_eq_zero.mpr (show (m+p : ℤ)-z=k by omega)
      simp [he']
    · rw [ih p (by omega)]
      simp

 

theorem coupledCoefficient_lower (n m z k p : ℕ) :
    coupledCoefficient n m z (k+1) p =
      (Real.sqrt (p : ℝ) * Real.sqrt ((n : ℝ)+1-p) * coupledCoefficient n m z k (p-1) +
        Real.sqrt (((z+k+1 : ℕ) : ℝ)-p) * Real.sqrt ((m : ℝ)+p-z-k) *
          coupledCoefficient n m z k p) /
        Real.sqrt (((k+1 : ℕ) : ℝ)*((n : ℝ)+m-2*z-k)) := by
  rw [coupledCoefficient]
  by_cases hp : p = 0
  · simp [hp]
  · rw [ite_eq_right hp, Real.sqrt_mul (Nat.cast_nonneg p)]

 
theorem affineSpin_atTop (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun Q : ℕ => a*Q-b) atTop atTop := by
  refine tendsto_atTop.mpr fun k => ?_
  filter_upwards [eventually_ge_atTop (k+b)] with Q hQ
  have hm : Q ≤ a*Q := by nlinarith only [ha]
  omega

 

theorem affineSpin_scaled_tendsto (a b : ℕ) (ha : 0 < a) :
    Tendsto (fun Q : ℕ => ((a*Q-b : ℕ) : ℝ) / Q) atTop (𝓝 (a : ℝ)) := by
  have h := tendsto_const_nhds (x := (a : ℝ)) |>.sub
    (tendsto_const_div_atTop_nhds_zero_nat (b : ℝ))
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (b+1)] with Q hQ
  have hm : Q ≤ a*Q := by nlinarith only [ha]
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  rw [Nat.cast_sub (by omega : b ≤ a*Q), Nat.cast_mul]
  field_simp

 

theorem affineSpin_ratio_tendsto (a b c d : ℕ) (ha : 0 < a) (hc : 0 < c) :
    Tendsto (fun Q : ℕ => ((c*Q-d : ℕ) : ℝ) /
      (((a*Q-b : ℕ) : ℝ) + ((c*Q-d : ℕ) : ℝ))) atTop
        (𝓝 ((c : ℝ) / (a+c : ℕ))) := by
  have h1 := affineSpin_scaled_tendsto a b ha
  have h2 := affineSpin_scaled_tendsto c d hc
  have h := h2.div (h1.add h2) (by positivity : (a : ℝ)+(c : ℝ) ≠ 0)
  simp only [Nat.cast_add]
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  simp only [Pi.div_apply]
  rw [← add_div]
  exact div_div_div_cancel_right₀ hQ0 _ _

 
theorem threeCoupling_tendsto (z k p : ℕ) :
    Tendsto (fun Q : ℕ => coupledCoefficient (2*Q-2) Q z k p) atTop
      (𝓝 (polynomialCouplingCoefficient (Real.sqrt (1/3)) (Real.sqrt (2/3)) z k p)) := by
  have h := coupledCoefficient_tendsto (fun Q => 2*Q-2) (fun Q => Q) (1/3)
    (affineSpin_atTop 2 2 (by norm_num)) tendsto_id
    (by simpa using affineSpin_ratio_tendsto 2 2 1 0 (by norm_num) (by norm_num)) z k p
  rw [oscillatorCoefficient_eq_polynomial _ (by norm_num) (by norm_num)] at h
  norm_num only [show (1 : ℝ)-1/3 = 2/3 by norm_num] at h
  exact h

 

theorem singlePairCoupling_tendsto (z k p : ℕ) :
    Tendsto (fun Q : ℕ => coupledCoefficient Q Q z k p) atTop
      (𝓝 (polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z k p)) := by
  have h := coupledCoefficient_tendsto (fun Q => Q) (fun Q => Q) (1/2)
    tendsto_id tendsto_id
    (by simpa using affineSpin_ratio_tendsto 1 0 1 0 (by norm_num) (by norm_num)) z k p
  rw [oscillatorCoefficient_eq_polynomial _ (by norm_num) (by norm_num)] at h
  norm_num only [show (1 : ℝ)-1/2 = 1/2 by norm_num] at h
  exact h

 

theorem doublePairCoupling_tendsto (r z k p : ℕ) :
    Tendsto (fun Q : ℕ => coupledCoefficient (2*Q-2) (2*Q-2*r) z k p) atTop
      (𝓝 (polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) z k p)) := by
  have h := coupledCoefficient_tendsto (fun Q => 2*Q-2) (fun Q => 2*Q-2*r) (1/2)
    (affineSpin_atTop 2 2 (by norm_num)) (affineSpin_atTop 2 (2*r) (by norm_num))
    (by convert affineSpin_ratio_tendsto 2 2 2 (2*r) (by norm_num) (by norm_num) using 1; norm_num) z k p
  rw [oscillatorCoefficient_eq_polynomial _ (by norm_num) (by norm_num)] at h
  norm_num only [show (1 : ℝ)-1/2 = 1/2 by norm_num] at h
  exact h

 

def sphericalCopyCoefficient (Q D T r p j k : ℕ) : ℝ :=
  if Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ j+k ∧ p+j+k = T then
    Real.sqrt 2 * coupledCoefficient Q Q r (j+k-r) j *
      coupledCoefficient (2*Q-2) (2*Q-2*r) (D-r) (T-D) p
  else 0

 

def planarCopyCoefficient (D T r p j k : ℕ) : ℝ :=
  if Odd r ∧ r ≤ D ∧ D ≤ T ∧ r ≤ j+k ∧ p+j+k = T then
    Real.sqrt 2 * polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) r (j+k-r) j *
      polynomialCouplingCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) (D-r) (T-D) p
  else 0

 

theorem sphericalCopyCoefficient_tendsto (D T r p j k : ℕ) :
    Tendsto (fun Q => sphericalCopyCoefficient Q D T r p j k) atTop
      (𝓝 (planarCopyCoefficient D T r p j k)) := by
  unfold sphericalCopyCoefficient planarCopyCoefficient
  split_ifs
  · exact ((singlePairCoupling_tendsto r (j+k-r) j).const_mul (Real.sqrt 2)).mul
      (doublePairCoupling_tendsto r (D-r) (T-D) p)
  · exact tendsto_const_nhds

end LaughlinFock
end

end OAI
