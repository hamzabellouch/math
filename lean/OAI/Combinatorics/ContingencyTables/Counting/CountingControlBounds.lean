import OAI.Combinatorics.ContingencyTables.Machines.ScalarScheduleBounds
import OAI.Combinatorics.ContingencyTables.Counting.CountingPhaseScalarProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingScheduleSizes

namespace OAI

/-! # Polynomial bounds for the observation and precision controls -/

namespace ContingencyTables.CountingControlBounds
open ScalarScheduleProgram CountingPhaseSchedule Polynomial
noncomputable section

def observationPolynomial : Polynomial ℕ :=
  CountingPhaseScalarProgram.observationNumerator.bound*(1600*(X+1)*X)^2+2
def returnPolynomial : Polynomial ℕ := CountingPhaseScalarProgram.returnCap.bound
def largePolynomial : Polynomial ℕ := X+observationPolynomial+returnPolynomial+1
def precisionPolynomial : Polynomial ℕ :=
  CountingPhaseScalarProgram.precisionBase.bound.comp largePolynomial+1600*(X+1)*X

lemma half_inverse_le (epsilon : ℚ) (M : ℕ) (h : 1/epsilon ≤ (M:ℚ)) :
    1/(epsilon/2) ≤ ((2*M:ℕ):ℚ) := by
  have hh := mul_le_mul_of_nonneg_left h (show (0:ℚ) ≤ 2 by norm_num)
  convert hh using 1 <;> push_cast <;> ring

lemma observations_bound (p W H M : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hp : p ≤ M) (hW : W ≤ M) (hH : H ≤ M) (hi : 1/epsilon ≤ (M:ℚ)) :
    observations p W H (tolerance H (epsilon/2)) ≤ observationPolynomial.eval M := by
  have hn := observations_le p W H (2*M) (epsilon/2) (by positivity)
    (half_inverse_le epsilon M hi)
  have hnumer := CountingPhaseScalarProgram.observationNumerator.eval_le_of_mem
    [p,W,H,0,0,0,0] M (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  rw [CountingPhaseScalarProgram.observationNumerator_value] at hnumer
  have ht : 800*(H+1)*(2*M) ≤ 1600*(M+1)*M := by
    calc
      _ = 1600*(H+1)*M := by ring
      _ ≤ _ := Nat.mul_le_mul_right M (Nat.mul_le_mul_left 1600 (Nat.add_le_add_right hH 1))
  refine hn.trans ?_
  simp only [observationBound,observationPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  exact Nat.add_le_add_right (Nat.mul_le_mul hnumer (Nat.pow_le_pow_left ht 2)) 2

lemma return_bound (p H T M : ℕ) (hp : p ≤ M) (hH : H ≤ M) (hT : T ≤ M) :
    returnCap p H T ≤ returnPolynomial.eval M := by
  have hb := CountingPhaseScalarProgram.returnCap.eval_le_of_mem [p,0,H,T,0,0,0] M (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  rwa [CountingPhaseScalarProgram.returnCap_value] at hb

lemma precision_bound (p W H T M : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hp : p ≤ M) (hW : W ≤ M) (hH : H ≤ M) (hT : T ≤ M)
    (hi : 1/epsilon ≤ (M:ℚ)) :
    precision H T (observations p W H (tolerance H (epsilon/2))) (returnCap p H T)
      (tolerance H (epsilon/2)) ≤ precisionPolynomial.eval M := by
  let N := observations p W H (tolerance H (epsilon/2))
  let R := returnCap p H T
  have hN : N ≤ observationPolynomial.eval M := observations_bound p W H M epsilon he hp hW hH hi
  have hR : R ≤ returnPolynomial.eval M := return_bound p H T M hp hH hT
  have hB : M ≤ largePolynomial.eval M := by
    simp only [largePolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hb := CountingPhaseScalarProgram.precisionBase.eval_le_of_mem [p,W,H,T,N,R,0]
    (largePolynomial.eval M) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      have hN' : N ≤ largePolynomial.eval M := by
        simp only [largePolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        omega
      have hR' : R ≤ largePolynomial.eval M := by
        simp only [largePolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        omega
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  rw [CountingPhaseScalarProgram.precisionBase_value] at hb
  have hc : ⌈1/tolerance H (epsilon/2)⌉₊ ≤ 1600*(M+1)*M := by
    apply (Nat.ceil_le.mpr (inverse_tolerance_le H (2*M) (epsilon/2) (by positivity)
      (half_inverse_le epsilon M hi))).trans
    calc
      800*(H+1)*(2*M)=1600*(H+1)*M := by ring
      _ ≤ _ := Nat.mul_le_mul_right M (Nat.mul_le_mul_left 1600 (Nat.add_le_add_right hH 1))
  simp only [precisionPolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change 1024*(H+1)*noiseCoefficient H T N R+⌈1/tolerance H (epsilon/2)⌉₊+1 ≤ _
  omega

end
end ContingencyTables.CountingControlBounds

end OAI
