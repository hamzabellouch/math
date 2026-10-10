import OAI.NumberTheory.JointDickman.Arithmetic.DivisorProductDifference

namespace OAI

/-! # An exponential bound for tails of finite positive Euler products -/
namespace JointDickman
open Finset Classical

theorem prod_one_add_le_exp_sum {ι : Type*} (S : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ S, 0 ≤ b i) :
    (∏ i ∈ S, (1+b i)) ≤ Real.exp (∑ i ∈ S, b i) := by
  rw [Real.exp_sum]
  apply prod_le_prod₀
  · intro i hi
    linarith [hb i hi]
  · intro i _
    simpa only [add_comm] using Real.add_one_le_exp (b i)

theorem exp_sub_one_le_exp_mul (x : ℝ) : Real.exp x-1 ≤ Real.exp x*x := by
  have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hh
  nlinarith

theorem prod_one_add_difference_bound {ι : Type*} [DecidableEq ι]
    {P Q : Finset ι} (hQP : Q ⊆ P) (b : ι → ℝ) (hb : ∀ i ∈ P, 0 ≤ b i) :
    0 ≤ (∏ i ∈ P, (1+b i))-(∏ i ∈ Q, (1+b i)) ∧
    (∏ i ∈ P, (1+b i))-(∏ i ∈ Q, (1+b i)) ≤
      Real.exp (∑ i ∈ P, b i)*(∑ i ∈ P \ Q, b i) := by
  let R := P \ Q
  have hbQ i hi := hb i (hQP hi)
  have hbR i (hi : i ∈ R) := hb i (mem_sdiff.mp hi).1
  have hP0 : 0 ≤ ∏ i ∈ Q, (1+b i) := prod_nonneg (fun i hi => by linarith [hbQ i hi])
  have hR1 : 1 ≤ ∏ i ∈ R, (1+b i) := one_le_prod₀ (fun i hi => by linarith [hbR i hi])
  have hid : (∏ i ∈ P, (1+b i))-(∏ i ∈ Q, (1+b i)) =
      (∏ i ∈ Q, (1+b i))*((∏ i ∈ R, (1+b i))-1) := by
    rw [← prod_sdiff hQP]
    dsimp only [R]
    ring
  rw [hid]
  refine ⟨mul_nonneg hP0 (sub_nonneg.mpr hR1),?_⟩
  have hprodQ := prod_one_add_le_exp_sum Q b hbQ
  have htail : (∏ i ∈ R, (1+b i))-1 ≤ Real.exp (∑ i ∈ R, b i)*(∑ i ∈ R, b i) :=
    (sub_le_sub_right (prod_one_add_le_exp_sum R b hbR) 1).trans (exp_sub_one_le_exp_mul _)
  have hh := mul_le_mul hprodQ htail (sub_nonneg.mpr hR1) (Real.exp_pos _).le
  refine hh.trans_eq ?_
  rw [← mul_assoc,← Real.exp_add]
  congr 1
  have hs : (∑ i ∈ Q, b i)+(∑ i ∈ R, b i) = ∑ i ∈ P, b i := by
    dsimp only [R]
    rw [add_comm,sum_sdiff hQP]
  rw [hs]

end JointDickman

end OAI
