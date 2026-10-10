import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # The numerical decay step in the harmonic level-set iteration -/

open Filter
open scoped Topology

noncomputable section
namespace RegularPointCoordinates

/-- A superlinear recurrence stays below a geometric barrier whenever
the two scalar barrier inequalities hold. -/
theorem superlinear_geometric_barrier {Y : ℕ → ℝ} {C b ε A q : ℝ}
    (hY : ∀ i, 0 ≤ Y i) (hC : 0 ≤ C) (hb : 0 ≤ b) (hε : 0 < ε)
    (hA : 0 < A) (hq : 0 < q) (hstart : Y 0 ≤ A)
    (hAq : C*A^ε ≤ q) (hbq : b*q^ε ≤ 1)
    (hrec : ∀ i, Y (i+1) ≤ C*b^i*(Y i)^(1+ε)) :
    ∀ i, Y i ≤ A*q^i := by
  intro i
  induction i with
  | zero => simpa only [pow_zero,mul_one] using hstart
  | succ i hi =>
    calc
      Y (i+1) ≤ C*b^i*(Y i)^(1+ε) := hrec i
      _ ≤ C*b^i*(A*q^i)^(1+ε) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hY i) hi (by linarith)) (mul_nonneg hC (pow_nonneg hb _))
      _ = A*(C*A^ε)*q^i*(b*q^ε)^i := by
        rw [Real.rpow_add (mul_pos hA (pow_pos hq _)),Real.rpow_one,
          Real.mul_rpow hA.le (pow_nonneg hq.le _),
          ← Real.rpow_pow_comm hq.le ε i,mul_pow]
        ring
      _ ≤ A*q*q^i*1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAq hA.le)
            (pow_nonneg hq.le _)
        · exact pow_le_one₀ (mul_nonneg hb (Real.rpow_nonneg hq.le _)) hbq
        · positivity
        · positivity
      _ = A*q^(i+1) := by rw [pow_succ]; ring

/-- For each superlinear recurrence there is a positive starting threshold
which forces convergence to zero. -/
theorem exists_superlinear_decay_threshold {C b ε : ℝ}
    (hC : 0 < C) (hb : 0 < b) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ Y : ℕ → ℝ,
      (∀ i, 0 ≤ Y i) → Y 0 ≤ A →
      (∀ i, Y (i+1) ≤ C*b^i*(Y i)^(1+ε)) → Tendsto Y atTop (𝓝 0) := by
  let t := 1/(2*b+2)
  have ht : 0 < t := by dsimp only [t]; positivity
  have ht1 : t < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  let q := t^(1/ε)
  have hq : 0 < q := Real.rpow_pos_of_pos ht _
  have hq1 : q < 1 := Real.rpow_lt_one ht.le ht1 (by positivity)
  have hqε : q^ε = t := by
    rw [← Real.rpow_mul ht.le]
    have he : (1/ε)*ε = 1 := by field_simp
    rw [he,Real.rpow_one]
  have hbq : b*q^ε ≤ 1 := by
    rw [hqε]
    dsimp only [t]
    rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr (by linarith)
  let A := (q/(C+1))^(1/ε)
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hAε : A^ε = q/(C+1) := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ q/(C+1))]
    have he : (1/ε)*ε = 1 := by field_simp
    rw [he,Real.rpow_one]
  have hAq : C*A^ε ≤ q := by
    rw [hAε]
    calc
      C*(q/(C+1)) = (C/(C+1))*q := by ring
      _ ≤ 1*q := mul_le_mul_of_nonneg_right
        ((div_le_one (by positivity)).mpr (by linarith)) hq.le
      _ = q := one_mul q
  refine ⟨A,hA,?_⟩
  intro Y hY hstart hrec
  have hbound := superlinear_geometric_barrier hY hC.le hb.le hε hA hq hstart hAq hbq hrec
  apply squeeze_zero hY hbound
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq.le hq1).const_mul A

end RegularPointCoordinates

end

end OAI
