import Mathlib
import OAI.Probability.LogConcave.JetEstimates.Slice

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators NNReal ENNReal

namespace TensorSum
variable {S : Type} [Fintype S]

def logDegree (A : TensorSum S) (j : ℕ) : ℕ :=
  ∑i,(A.term i).atom.expression.profileConstant*(j+1)

def logCoefficient (A : TensorSum S) (j : ℕ) (p : ℝ≥0∞) : ℝ :=
  ∑i,polynomialBudget (A.term i).coefficient*
    (4*((A.term i).atom.expression.profileConstant:ℝ)*(p.toReal+j+1))^
      ((A.term i).atom.expression.profileConstant*(j+1))

omit [Fintype S] in
lemma logCoefficient_nonneg (A : TensorSum S) (j : ℕ) (p : ℝ≥0∞) :
    0≤A.logCoefficient j p := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (polynomialBudget_nonneg _) (by positivity)

omit [Fintype S] in
lemma momentBudget_polylog (A : TensorSum S) (d j : ℕ) (p : ℝ≥0∞) :
    (A.momentBudget d j p).toReal≤
      A.logCoefficient j p*(1+Real.log ((d:ℝ)+1))^(A.logDegree j) := by
  have hl : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  have ht : 1≤1+Real.log ((d:ℝ)+1) := by linarith
  have hf (i : A.index) :
      ENNReal.ofReal (polynomialBudget (A.term i).coefficient)*
      ((4*((A.term i).atom.expression.profileConstant:ℝ≥0∞))*
        ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^
        ((A.term i).atom.expression.profileConstant*(j+1))≠⊤ := by
    apply ne_of_lt
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (by norm_num) (ENNReal.natCast_lt_top _)) ENNReal.ofReal_lt_top))
  rw [momentBudget,ENNReal.toReal_sum (fun i _ => hf i),logCoefficient,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast,ENNReal.toReal_ofReal (polynomialBudget_nonneg _),
    ENNReal.toReal_ofReal (by positivity : 0≤p.toReal+(j:ℝ)+Real.log ((d:ℝ)+1)+1)]
  let c := (A.term i).atom.expression.profileConstant
  let n := c*(j+1)
  have hb : 4*(c:ℝ)*(p.toReal+j+Real.log ((d:ℝ)+1)+1)≤
      (4*(c:ℝ)*(p.toReal+j+1))*(1+Real.log ((d:ℝ)+1)) := by
    have hh : 0≤(p.toReal+(j:ℝ))*Real.log ((d:ℝ)+1) := by positivity
    have hh' := mul_nonneg (by positivity : 0≤4*(c:ℝ)) hh
    nlinarith
  have hn : n≤A.logDegree j := by
    dsimp [n,c,logDegree]
    exact Finset.single_le_sum (f:=fun i : A.index => (A.term i).atom.expression.profileConstant*(j+1)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  calc
    _ ≤ polynomialBudget (A.term i).coefficient*
        ((4*(c:ℝ)*(p.toReal+j+1))*(1+Real.log ((d:ℝ)+1)))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb _) (polynomialBudget_nonneg _)
    _ = polynomialBudget (A.term i).coefficient*(4*(c:ℝ)*(p.toReal+j+1))^n*
        (1+Real.log ((d:ℝ)+1))^n := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hn) (by
      exact mul_nonneg (polynomialBudget_nonneg _) (by positivity))
end TensorSum
end LogConcaveSampling

end

end

end

end OAI
