import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.FiniteEntropy
variable {X A : Type*} [Fintype X] [Fintype A]

lemma weighted_cauchy (w f g : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * f x * g x)^2 ≤ (∑ x, w x * (f x)^2) * ∑ x, w x * (g x)^2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro x _; exact mul_nonneg (hw x) (sq_nonneg _)
  · intro x _; exact mul_nonneg (hw x) (sq_nonneg _)
  · intro x _; apply le_of_eq; ring

lemma pooled_bias_bound (tag : X → A) (w f b : X → ℝ) (L Z : A → ℝ) {C : ℝ}
    (hw : ∀ x, 0 ≤ w x) (hL : ∀ a, 0 ≤ L a) (hC : 0 ≤ C)
    (hZ : ∀ a, Z a = ∑ x, if tag x = a then w x*f x*b x else 0)
    (hcost : ∀ a, (∑ x, if tag x = a then w x*(f x)^2 else 0) ≤ C*L a) :
    (∑ a, (Z a)^2 / L a) ≤ C * ∑ x, w x*(b x)^2 := by
  have hpoint (a : A) : (Z a)^2 / L a ≤
      C * ∑ x, if tag x = a then w x*(b x)^2 else 0 := by
    let w' : X → ℝ := fun x => if tag x = a then w x else 0
    have hw' (x : X) : 0 ≤ w' x := by
      dsimp [w']
      split_ifs
      · exact hw x
      · exact le_rfl
    have hcs := weighted_cauchy w' f b hw'
    have h1 : (∑ x, w' x*f x*b x) = Z a := by
      rw [hZ a]; apply Finset.sum_congr rfl
      intro x _; dsimp [w']; split_ifs <;> simp
    have h2 : (∑ x, w' x*(f x)^2) ≤ C*L a := by
      convert hcost a using 1
      apply Finset.sum_congr rfl
      intro x _; dsimp [w']; split_ifs <;> simp
    have h3 : (∑ x, w' x*(b x)^2) =
        ∑ x, if tag x = a then w x*(b x)^2 else 0 := by
      apply Finset.sum_congr rfl
      intro x _; dsimp [w']; split_ifs <;> simp
    have hnon : 0 ≤ ∑ x, w' x*(b x)^2 :=
      Finset.sum_nonneg (fun x _ => mul_nonneg (hw' x) (sq_nonneg _))
    rw [h1] at hcs
    rcases eq_or_lt_of_le (hL a) with hz | hp
    · simp only [← hz, div_zero]
      rw [← h3]
      exact mul_nonneg hC hnon
    · apply (div_le_iff₀ hp).mpr
      rw [← h3]
      calc
        (Z a)^2 ≤ (∑ x, w' x*(f x)^2)*(∑ x, w' x*(b x)^2) := hcs
        _ ≤ (C*L a)*(∑ x, w' x*(b x)^2) := mul_le_mul_of_nonneg_right h2 hnon
        _ = _ := by ring
  calc
    (∑ a, (Z a)^2/L a) ≤ ∑ a, C*∑ x, if tag x = a then w x*(b x)^2 else 0 :=
      Finset.sum_le_sum (fun a _ => hpoint a)
    _ = C * ∑ x, w x*(b x)^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      simp

lemma pooled_two_weight_bound (tag : X → A) (z u v : X → ℝ) (L Z : A → ℝ) {C : ℝ}
    (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (hz : ∀ x, (z x)^2 ≤ u x*v x) (hL : ∀ a, 0 ≤ L a) (hC : 0 ≤ C)
    (hZ : ∀ a, Z a = ∑ x, if tag x = a then z x else 0)
    (hcost : ∀ a, (∑ x, if tag x = a then u x else 0) ≤ C*L a) :
    (∑ a, (Z a)^2 / L a) ≤ C * ∑ x, v x := by
  have hpoint (a : A) : (Z a)^2 / L a ≤
      C * ∑ x, if tag x = a then v x else 0 := by
    have hcs : (∑ x, if tag x = a then z x else 0)^2 ≤
        (∑ x, if tag x = a then u x else 0)*
        (∑ x, if tag x = a then v x else 0) := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro x _; split_ifs; exact hu x; exact le_rfl
      · intro x _; split_ifs; exact hv x; exact le_rfl
      · intro x _; split_ifs; exact hz x; norm_num
    rw [← hZ a] at hcs
    have hnon : 0 ≤ ∑ x, if tag x = a then v x else 0 := by
      apply Finset.sum_nonneg
      intro x _; split_ifs; exact hv x; exact le_rfl
    rcases eq_or_lt_of_le (hL a) with he | hp
    · rw [← he, div_zero]
      exact mul_nonneg hC hnon
    · apply (div_le_iff₀ hp).mpr
      calc
        (Z a)^2 ≤ (∑ x, if tag x = a then u x else 0)*
            (∑ x, if tag x = a then v x else 0) := hcs
        _ ≤ (C*L a)*(∑ x, if tag x = a then v x else 0) :=
          mul_le_mul_of_nonneg_right (hcost a) hnon
        _ = _ := by ring
  calc
    (∑ a, (Z a)^2/L a) ≤ ∑ a, C*∑ x, if tag x = a then v x else 0 :=
      Finset.sum_le_sum (fun a _ => hpoint a)
    _ = C * ∑ x, v x := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      simp

end CriticalPercolation.FiniteEntropy

end
end

end OAI
