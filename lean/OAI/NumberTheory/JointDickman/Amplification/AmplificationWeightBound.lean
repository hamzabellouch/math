import OAI.NumberTheory.JointDickman.Probability.AmplificationFairKernel
import OAI.NumberTheory.JointDickman.Counting.CoefficientProductSupport

namespace OAI

/-! # The unique-quotient bound used when removing coprimality -/

namespace JointDickman
open Finset

open Classical in
theorem amplificationScalarWeight_bounds (B j : ℕ) (T : ℝ) (c b a : ℕ) :
    0 ≤ amplificationScalarWeight B j T c b a ∧
      amplificationScalarWeight B j T c b a ≤ coefficientScale B := by
  unfold amplificationScalarWeight
  split_ifs
  · have h1 := amplificationBump_bounds (Real.log c/B)
    have h2 := amplificationBump_bounds (a/(T*c))
    have h3 := amplificationBump_bounds (b/(T*c))
    have hprod : 0 ≤ amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c)) := mul_nonneg (mul_nonneg h1.1 h2.1) h3.1
    have hprod1 : amplificationBump (Real.log c/B)*amplificationBump (a/(T*c))*
        amplificationBump (b/(T*c)) ≤ 1 := by
      calc
        _ ≤ (1 : ℝ)*1*1 := mul_le_mul (mul_le_mul h1.2 h2.2 h2.1 (by norm_num))
          h3.2 h3.1 (by norm_num)
        _ = _ := by norm_num
    exact ⟨mul_nonneg (coefficientWeight_nonneg B c) hprod,
      (mul_le_of_le_one_right (coefficientWeight_nonneg B c) hprod1).trans
        (coefficientWeight_le_scale B c)⟩
  · exact ⟨le_rfl,coefficientScale_nonneg B⟩

open Classical in
theorem amplificationScalarWeight_sum_le (B : ℕ) {j : ℕ} (hj : 0 < j)
    (T : ℝ) (V a b : ℕ) :
    (∑ c ∈ Ioc 0 V, amplificationScalarWeight B j T c b a) ≤ coefficientScale B := by
  let C := (Ioc 0 V).filter (fun c => a = b+j*c)
  have hcard : C.card ≤ 1 := by
    apply card_le_one.mpr
    intro c hc d hd
    have hc' := (mem_filter.mp hc).2
    have hd' := (mem_filter.mp hd).2
    exact Nat.mul_left_cancel hj (Nat.add_left_cancel (hc'.symm.trans hd'))
  calc
    _ = ∑ c ∈ C, amplificationScalarWeight B j T c b a := by
      symm
      apply sum_subset (filter_subset _ _)
      intro c hc hnot
      have hrel : a ≠ b+j*c := by
        intro he
        exact hnot (mem_filter.mpr ⟨hc,he⟩)
      simp [amplificationScalarWeight,hrel]
    _ ≤ ∑ _c ∈ C, coefficientScale B :=
      sum_le_sum (fun c _ => (amplificationScalarWeight_bounds B j T c b a).2)
    _ = (C.card : ℝ)*coefficientScale B := by simp
    _ ≤ (1 : ℝ)*coefficientScale B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (coefficientScale_nonneg B)
    _ = _ := one_mul _

open Classical in
noncomputable def amplificationProductWeight (B j : ℕ) (T : ℝ) (V a b : ℕ) : ℝ :=
  B*∑ c ∈ Ioc 0 V, amplificationScalarWeight B j T c b a

theorem amplificationProductWeight_bounds (B : ℕ) {j : ℕ} (hj : 0 < j)
    (T : ℝ) (V a b : ℕ) :
    0 ≤ amplificationProductWeight B j T V a b ∧
      amplificationProductWeight B j T V a b ≤ (B : ℝ)*coefficientScale B := by
  unfold amplificationProductWeight
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (sum_nonneg
    (fun c _ => (amplificationScalarWeight_bounds B j T c b a).1)),
    mul_le_mul_of_nonneg_left (amplificationScalarWeight_sum_le B hj T V a b) (Nat.cast_nonneg _)⟩

end JointDickman

end OAI
