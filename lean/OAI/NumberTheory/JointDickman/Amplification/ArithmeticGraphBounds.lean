import OAI.NumberTheory.JointDickman.Probability.ArithmeticGraphKernel

namespace OAI

/-! # Positivity and support of the actual arithmetic graph kernel -/

namespace JointDickman
open Finset

theorem arithmeticGraphPairWeight_nonneg (B L : ℕ) (τ C : ℝ)
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (hu : ∀ c, 0 ≤ u c)
    (hv : ∀ a c, 0 ≤ v a c) (a b c : ℕ) (j : ℤ) (n : ℕ) :
    0 ≤ arithmeticGraphPairWeight B L τ C u v a b c j n := by
  have hA (d l : ℕ) : 0 ≤ regularCoefficientWeight B L τ C d *
      arithmeticResidueWeight B L τ C l * v d c :=
    mul_nonneg (mul_nonneg (regularCoefficientWeight_nonneg B L τ C d)
      (regularResidueWeight_nonneg B L τ C _)) (hv d c)
  have hC : 0 ≤ u c * regularCoefficientWeight B L τ C c *
      arithmeticResidueWeight B L τ C (divisorEdgeInverse a b c n) :=
    mul_nonneg (mul_nonneg (hu c) (regularCoefficientWeight_nonneg B L τ C c))
      (regularResidueWeight_nonneg B L τ C _)
  exact mul_nonneg (mul_nonneg hC (hA a (n/b))) (hA b (((n : ℤ)+j).toNat/a))

theorem rawArithmeticGraphKernel_nonneg (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (j : ℤ) (n : ℕ) : 0 ≤ rawArithmeticGraphKernel B L τ C T N j n := by
  classical
  apply sum_nonneg
  intro i _
  split_ifs
  · exact arithmeticGraphPairWeight_nonneg B L τ C (amplificationOuterWeight B)
      (amplificationInnerWeight T) (fun _ => (amplificationBump_bounds _).1)
      (fun _ _ => (amplificationBump_bounds _).1) _ _ _ _ _
  · rfl

theorem rawArithmeticGraphKernel_zero_lag (B L : ℕ) (τ C : ℝ) (T N n : ℕ) :
    rawArithmeticGraphKernel B L τ C T N 0 n = 0 := by
  classical
  apply sum_eq_zero
  intro i hi
  have hne := (mem_filter.mp hi).2.2.1
  change coefficientPairLag i.1 i.2.1 i.2.2 ≠ 0 at hne
  have hn : ¬ (graphTripleLag i = 0 ∧ n ∈ graphTripleEdges N i) := fun h => hne h.1
  exact ite_eq_right hn

theorem rawArithmeticGraphKernel_large_lag (B L : ℕ) (τ C : ℝ)
    (T N : ℕ) (j : ℤ) (n : ℕ) (hj : T ≤ j.natAbs) :
    rawArithmeticGraphKernel B L τ C T N j n = 0 := by
  classical
  apply sum_eq_zero
  intro i hi
  have hlt := (mem_filter.mp hi).2.2.2.1
  have hn : ¬ (graphTripleLag i = j ∧ n ∈ graphTripleEdges N i) := by
    intro h
    change (graphTripleLag i).natAbs < T at hlt
    rw [h.1] at hlt
    omega
  exact ite_eq_right hn

end JointDickman

end OAI
