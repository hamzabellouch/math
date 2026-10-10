import Mathlib
import OAI.Analysis.LaughlinFock.PairIdentification
import OAI.Analysis.LaughlinFock.SpinTails
import OAI.Analysis.LaughlinFock.SwapCompression

namespace OAI

/-! Exchange Spectrum. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators

theorem sphericalPairCoefficient_coupled {Q p : ℕ} (hQ : 1 ≤ Q)
    (hp : p ≤ 2*Q-2) (i j : ℕ) :
    Real.sqrt 2 * coupledVector Q Q 1 p i j = sphericalPairCoefficient Q p i j := by
  rw [sphericalPairCoefficient_eq_normalized hQ hp, normalizedPairGrid_eq_coupled hQ hp]

theorem sphericalPairCoefficient_top {Q : ℕ} (hQ : 1 ≤ Q) (i j : ℕ) :
    sphericalPairCoefficient Q 0 i j =
      (if i=1 ∧ j=0 then 1 else 0) - (if i=0 ∧ j=1 then 1 else 0) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  by_cases ht : i+j=1
  · have hcases : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by omega
    rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [sphericalPairCoefficient, hq]
  · simp only [sphericalPairCoefficient, zero_add, ite_eq_right ht]
    rw [ite_eq_right (by omega : ¬(i=1 ∧ j=0)), ite_eq_right (by omega : ¬(i=0 ∧ j=1))]
    ring

theorem pairCoupled_top {Q : ℕ} (hQ : 1 ≤ Q) (i j : ℕ) :
    coupledVector Q Q 1 0 i j =
      ((if i=1 ∧ j=0 then 1 else 0) - (if i=0 ∧ j=1 then 1 else 0)) / Real.sqrt 2 := by
  apply (eq_div_iff (by positivity : Real.sqrt (2:ℝ) ≠ 0)).mpr
  rw [mul_comm, sphericalPairCoefficient_coupled hQ (by omega), sphericalPairCoefficient_top hQ]

 

theorem pairTensorProject_top {Q : ℕ} (hQ : 1 ≤ Q) (f : CubeVector) (k : ℕ) :
    pairTensorProject Q f 0 k = (f 1 0 k - f 0 1 k) / Real.sqrt 2 := by
  simp only [pairTensorProject, LinearMap.coe_mk, AddHom.coe_mk, gridInner, pairCoupled_top hQ]
  simp only [sub_div, sub_mul, Finset.sum_sub_distrib]
  simp only [ite_and, ite_div, zero_div, ite_mul, zero_mul, one_div]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_range,
    show 0 < Q+1 by omega, show 1 < Q+1 by omega, ite_true, Finset.sum_const_zero]
  ring

 
theorem pairTensorEmbed_apply {Q p i j : ℕ} (hij : i+j=p+1) (hp : p ≤ 2*Q-2)
    (f : GridVector) (k : ℕ) :
    pairTensorEmbed Q f i j k = coupledVector Q Q 1 p i j * f p k := by
  simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_eq_single p
  · intro r _ hr
    rw [coupledVector_layer Q Q 1 r i j (by omega), zero_mul]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

theorem pairTensorEmbed_zero_zero (Q : ℕ) (f : GridVector) (k : ℕ) :
    pairTensorEmbed Q f 0 0 k = 0 := by
  simp only [pairTensorEmbed, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_eq_zero
  intro p _
  rw [coupledVector_layer Q Q 1 p 0 0 (by omega), zero_mul]

 

theorem pairSwapCompression_highest {Q z : ℕ} (hQ : 2 ≤ Q)
    (hz : z ≤ Q) (hz0 : 1 ≤ z) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q z 0) 0 z =
      (sphericalPairCoefficient Q z 1 z * highestCoefficient (2*Q-2) Q z z -
        sphericalPairCoefficient Q (z-1) 0 z * highestCoefficient (2*Q-2) Q z (z-1))/2 := by
  have h2 : Real.sqrt (2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorProject_top (by omega : 1 ≤ Q),
    swap23, LinearMap.coe_mk, AddHom.coe_mk]
  rw [pairTensorEmbed_apply (by omega : 1+z=z+1) (by omega),
    pairTensorEmbed_apply (by omega : 0+z=(z-1)+1) (by omega)]
  rw [show coupledVector (2*Q-2) Q z 0 z 0 = highestCoefficient (2*Q-2) Q z z by
        simp [coupledVector, coupledCoefficient],
    show coupledVector (2*Q-2) Q z 0 (z-1) 1 = highestCoefficient (2*Q-2) Q z (z-1) by
      simp [coupledVector, coupledCoefficient, show z-1+1=z by omega]]
  rw [← sphericalPairCoefficient_coupled (by omega : 1 ≤ Q) (by omega),
    ← sphericalPairCoefficient_coupled (by omega : 1 ≤ Q) (by omega)]
  field_simp
  rw [h2]

 
theorem pairSwapCompression_highest_zero {Q : ℕ} (hQ : 2 ≤ Q) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q 0 0) 0 0 =
      highestCoefficient (2*Q-2) Q 0 0 / 2 := by
  have h2 : Real.sqrt (2:ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [pairSwapCompression, LinearMap.comp_apply, pairTensorProject_top (by omega : 1 ≤ Q),
    swap23, LinearMap.coe_mk, AddHom.coe_mk]
  rw [pairTensorEmbed_apply (p := 0) (i := 1) (j := 0) rfl (by omega), pairTensorEmbed_zero_zero,
    pairCoupled_top (by omega : 1 ≤ Q)]
  simp only [coupledVector, coupledCoefficient, add_zero, ite_true, sub_zero, and_self,
    zero_ne_one, and_false, ite_false, div_mul_eq_mul_div]
  field_simp
  rw [h2]

 
theorem sphericalPairCoefficient_edge_one {Q : ℕ} (hQ : 1 ≤ Q) (z : ℕ) :
    sphericalPairCoefficient Q z 1 z = (1-z : ℝ) * Real.sqrt (fallingRatio Q z) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hz : (z.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero z
  simp only [sphericalPairCoefficient, add_comm 1 z, ite_true,
    Nat.descFactorial_one, Nat.factorial_one, Nat.cast_one, mul_one]
  congr 2
  unfold fallingRatio
  field_simp

 

theorem sphericalPairCoefficient_edge_zero {Q z : ℕ} (hQ : 1 ≤ Q) (hz0 : 1 ≤ z) :
    sphericalPairCoefficient Q (z-1) 0 z = -(z:ℝ) *
      Real.sqrt ((((Q-1).descFactorial (z-1) : ℝ) / (2*Q-2).descFactorial (z-1)) / z) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hf : ((z-1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (z-1)
  have he : Q.descFactorial z = Q * (Q-1).descFactorial (z-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hQ, ← Nat.sub_add_cancel hz0]
    rw [Nat.succ_descFactorial_succ, Nat.sub_add_cancel hQ]
  have hez : z.factorial = z * (z-1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hz0]
    rw [Nat.factorial_succ, Nat.sub_add_cancel hz0]
  simp only [sphericalPairCoefficient, Nat.zero_add, Nat.sub_add_cancel hz0, ite_true,
    Nat.cast_zero, zero_sub, Nat.descFactorial_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
  congr 2
  rw [he, hez, Nat.cast_mul, Nat.cast_mul]
  field_simp

 
theorem sqrt_mul_sqrt_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.sqrt (y*x) * Real.sqrt (x/y) = x := by
  rw [← Real.sqrt_mul (mul_nonneg hy.le hx)]
  convert Real.sqrt_mul_self hx using 2
  field_simp

 

theorem fallingRatio_penultimate {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (hz0 : 1 ≤ z) :
    ((Q-1).descFactorial (z-1) : ℝ) / (2*Q-2).descFactorial (z-1) =
      fallingRatio Q z * ((2*Q-1-z : ℝ)/Q) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  have hd : ((2*Q-2).descFactorial (z-1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (show z-1 ≤ 2*Q-2 by omega)).ne'
  have he : Q.descFactorial z = Q * (Q-1).descFactorial (z-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel (by omega : 1 ≤ Q), ← Nat.sub_add_cancel hz0]
    rw [Nat.succ_descFactorial_succ, Nat.sub_add_cancel (by omega : 1 ≤ Q)]
  have he' : (2*Q-2).descFactorial z = (2*Q-2-(z-1)) * (2*Q-2).descFactorial (z-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hz0]
    rw [Nat.descFactorial_succ]
  have hw : (2*Q-2-(z-1) : ℕ) = 2*Q-1-z := by omega
  have hc : ((2*Q-1-z : ℕ) : ℝ) = 2*(Q:ℝ)-1-z := by
    rw [Nat.cast_sub (by omega : z ≤ 2*Q-1), Nat.cast_sub (by omega : 1 ≤ 2*Q)]
    push_cast
    rfl
  have hdz : (2*(Q:ℝ)-1-z) ≠ 0 := by
    rw [← hc]
    exact_mod_cast (show 2*Q-1-z ≠ 0 by omega)
  rw [fallingRatio, he, he', hw, Nat.cast_mul, Nat.cast_mul, hc]
  field_simp [hq, hd, hdz, mul_comm (Q:ℝ) 2]

 

theorem pairSwapCompression_scalar {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q z 0) 0 z =
      (-gramShift Q z / 2) * highestCoefficient (2*Q-2) Q z 0 := by
  by_cases hz0 : z=0
  · subst z
    rw [pairSwapCompression_highest_zero hQ]
    simp [gramShift, fallingRatio, div_eq_mul_inv, mul_comm]
  · have hzp : 1 ≤ z := by omega
    have hzn : z ≤ 2*Q-2 := by omega
    rw [pairSwapCompression_highest hQ hz hzp, sphericalPairCoefficient_edge_one (by omega),
      sphericalPairCoefficient_edge_zero (by omega) hzp,
      highestCoefficient_last hzn hz, highestCoefficient_penultimate hzn hz hzp]
    let x : ℝ := ((Q-1).descFactorial (z-1) : ℝ) / (2*Q-2).descFactorial (z-1)
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hroot : Real.sqrt ((z:ℝ) * (Q-1).descFactorial (z-1) / (2*Q-2).descFactorial (z-1)) =
        Real.sqrt ((z:ℝ)*x) := by congr 1; dsimp [x]; ring
    rw [hroot]
    change ((1-(z:ℝ))*Real.sqrt (fallingRatio Q z) *
        ((-1:ℝ)^z * Real.sqrt (fallingRatio Q z) * highestCoefficient (2*Q-2) Q z 0) -
      (-(z:ℝ)*Real.sqrt (x/z)) * ((-1:ℝ)^(z-1) * Real.sqrt ((z:ℝ)*x) *
        highestCoefficient (2*Q-2) Q z 0)) / 2 = _
    have hsign : (-1:ℝ)^(z-1) = -(-1:ℝ)^z := by
      conv_rhs => rw [← Nat.sub_add_cancel hzp, pow_succ]
      ring
    have hs : Real.sqrt (fallingRatio Q z) ^ 2 = fallingRatio Q z :=
      Real.sq_sqrt (fallingRatio_nonneg Q z)
    have hs' : Real.sqrt ((z:ℝ)*x) * Real.sqrt (x/z) = x :=
      sqrt_mul_sqrt_div hx (by exact_mod_cast hzp)
    calc
      _ = ((-1:ℝ)^z * ((1-(z:ℝ)) * Real.sqrt (fallingRatio Q z)^2 -
          (z:ℝ)*(Real.sqrt ((z:ℝ)*x)*Real.sqrt (x/z)))) / 2 *
            highestCoefficient (2*Q-2) Q z 0 := by rw [hsign]; ring
      _ = ((-1:ℝ)^z * ((1-(z:ℝ))*fallingRatio Q z - (z:ℝ)*x)) / 2 *
            highestCoefficient (2*Q-2) Q z 0 := by rw [hs, hs']
      _ = _ := by
        rw [show x = fallingRatio Q z * ((2*Q-1-z : ℝ)/Q) from fallingRatio_penultimate hQ hz hzp]
        unfold gramShift
        have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
        field_simp
        ring

 

theorem pairSwapCompression_eigenvector {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (k : ℕ) :
    pairSwapCompression Q (coupledVector (2*Q-2) Q z k) =
      (-gramShift Q z / 2) • coupledVector (2*Q-2) Q z k := by
  rw [pairSwapCompression_coupled hQ hz, pairSwapCompression_scalar hQ hz,
    mul_div_cancel_right₀ _ (highestCoefficient_first_ne_zero (by omega))]

end LaughlinFock
end

end OAI
