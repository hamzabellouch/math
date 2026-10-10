import Mathlib

namespace OAI

namespace Erdos970


namespace ErdosOddEulerCorrection

noncomputable def correction (k : ℕ) : ℝ := 1-1/((k : ℝ)+2)^2

theorem correction_nonneg (k : ℕ) : 0 ≤ correction k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp : (0 : ℝ) < ((k : ℝ)+2)^2 := by positivity
  apply sub_nonneg.mpr
  apply (div_le_one hp).mpr
  nlinarith

theorem correction_le_one (k : ℕ) : correction k ≤ 1 := by
  dsimp [correction]
  have : (0 : ℝ) ≤ 1/((k : ℝ)+2)^2 := by positivity
  linarith

theorem correction_range (N : ℕ) :
    (∏ k ∈ Finset.range N, correction k) = ((N : ℝ)+2)/(2*((N : ℝ)+1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ,ih]
    dsimp [correction]
    push_cast
    have h1 : (N : ℝ)+1 ≠ 0 := by positivity
    have h2 : (N : ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring

theorem correction_finite_lower (S : Finset ℕ) :
    (1 : ℝ)/2 ≤ ∏ k ∈ S, correction k := by
  let N := S.sup id+1
  have hS : S ⊆ Finset.range N := by
    intro k hk
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀ hS
    (fun k _ => correction_nonneg k) (fun k _ _ => correction_le_one k)
  have hhalf : (1 : ℝ)/2 ≤ ∏ k ∈ Finset.range N, correction k := by
    rw [correction_range]
    apply (le_div_iff₀ (show (0 : ℝ) < 2*((N : ℝ)+1) by positivity)).mpr
    linarith
  exact hhalf.trans hprod

theorem odd_correction_product_lower (P : Finset ℕ) (hP : ∀ p ∈ P,3 ≤ p) :
    (1 : ℝ)/2 ≤ ∏ p ∈ P, (1-1/((p : ℝ)-1)^2) := by
  classical
  have h := correction_finite_lower (P.image (fun p => p-3))
  rw [Finset.prod_image (fun p hp q hq he => by have := hP p hp; have := hP q hq; omega)] at h
  have he : (∏ p ∈ P, correction (p-3)) = ∏ p ∈ P, (1-1/((p : ℝ)-1)^2) := by
    apply Finset.prod_congr rfl
    intro p hp
    dsimp [correction]
    rw [Nat.cast_sub (hP p hp)]
    norm_num only [Nat.cast_ofNat]
    rw [show (p : ℝ)-3+2=(p : ℝ)-1 by ring]
  rwa [he] at h

theorem odd_two_class_factorization (P : Finset ℕ) (hP : ∀ p ∈ P,3 ≤ p) :
    (∏ p ∈ P, (1-2/(p : ℝ))) =
      (∏ p ∈ P, (1-1/((p : ℝ)-1)^2))*(∏ p ∈ P, (1-1/(p : ℝ)))^2 := by
  rw [← Finset.prod_pow,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hP p hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ)-1 ≠ 0 := by linarith
  field_simp
  ring

theorem odd_two_class_product_lower (P : Finset ℕ) (hP : ∀ p ∈ P,3 ≤ p) :
    (1 : ℝ)/2*(∏ p ∈ P, (1-1/(p : ℝ)))^2 ≤ ∏ p ∈ P, (1-2/(p : ℝ)) := by
  rw [odd_two_class_factorization P hP]
  exact mul_le_mul_of_nonneg_right (odd_correction_product_lower P hP) (sq_nonneg _)

end ErdosOddEulerCorrection


end Erdos970

end OAI
