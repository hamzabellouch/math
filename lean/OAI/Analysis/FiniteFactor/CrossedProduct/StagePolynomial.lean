import OAI.Analysis.FiniteFactor.CrossedProduct.StageOperator
import OAI.Analysis.FiniteFactor.Contradiction

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- The lower bound uses the very epsilon fixed by the recursive source
stage, which also occurs in its decay budget. No second choice is substituted. -/
theorem sourceStage_polynomial_lower (j : ℕ) (A B : ℤ → ℂ)
    (hA : ∀ v : ℤ, -((sourceStageState j).K : ℤ) ≤ v → v ≤ (sourceStageState j).K →
      ‖A v‖ ≤ (sourceStageState j).D)
    (hB : ∀ v : ℤ, -((sourceStageState j).K : ℤ) ≤ v → v ≤ (sourceStageState j).K →
      ‖B v‖ ≤ (sourceStageState j).D)
    (hA0 : 1/((j : ℝ)+1) ≤ ‖A 0‖) (hB0 : 1/((j : ℝ)+1) ≤ ‖B 0‖) :
    (sourceStage j).ε ≤ coefficientMass (sourceStageState j).K A B := by
  let K := (sourceStageState j).K
  let a : Coefficients K := fun i => A ((i.val : ℤ)-K)
  let b : Coefficients K := fun i => B ((i.val : ℤ)-K)
  have ha : ∀ i, ‖a i‖ ≤ (sourceStageState j).D := by
    intro i
    apply hA <;> have := i.isLt <;> omega
  have hb : ∀ i, ‖b i‖ ≤ (sourceStageState j).D := by
    intro i
    apply hB <;> have := i.isLt <;> omega
  have ha0 : 1/((j : ℝ)+1) ≤ ‖a ⟨K,by omega⟩‖ := by simpa [a] using hA0
  have hb0 : 1/((j : ℝ)+1) ≤ ‖b ⟨K,by omega⟩‖ := by simpa [b] using hB0
  obtain ⟨i,hi⟩ := (sourceStage j).polynomial a b ha hb ha0 hb0
  have hiK : i.val ≤ 2*K := by have := i.isLt; omega
  have he : -((2*K-i.val : ℕ) : ℤ) = (i.val : ℤ)-2*K := by omega
  have hh : (sourceStage j).ε ≤ ‖laurentProductCoefficient K A B (-((2*K-i.val : ℕ) : ℤ))‖ := by
    rw [he]
    change (sourceStage j).ε ≤ ‖productCoefficient (K := K)
      (fun i => A ((i.val : ℤ)-K)) (fun i => B ((i.val : ℤ)-K)) i.val‖ at hi
    rw [shifted_productCoefficient K A B i.val] at hi
    exact hi
  apply hh.trans
  change _ ≤ ∑ n ∈ Finset.range (2*K+1), ‖laurentProductCoefficient K A B (-(n : ℤ))‖
  exact Finset.single_le_sum (s := Finset.range (2*K+1)) (a := 2*K-i.val)
    (fun i _ => norm_nonneg (laurentProductCoefficient K A B (-(i : ℤ))))
    (Finset.mem_range.mpr (by omega))

/-- The same source epsilon bounds the total permitted expected error. -/
theorem sourceStage_error_budget (j : ℕ) :
    (2*((sourceStageState j).K : ℝ)+1) *
      (Real.exp (-(sourceStage j).L)+2*Real.exp (-(sourceStage j).L/800)) ≤
        (sourceStage j).ε/((j : ℝ)+1) := by
  have hL : 0 ≤ (sourceStage j).L :=
    (zero_le_one.trans (sourceStageState j).previousL_ge).trans (sourceStage j).L_ge
  have hh := mul_le_mul_of_nonneg_left (exponential_tail_relaxation hL)
    (show (0 : ℝ) ≤ 2*((sourceStageState j).K : ℝ)+1 by positivity)
  apply hh.trans
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,mul_assoc] using (sourceStage j).decay

end
end FiniteFactor

end OAI
