import Mathlib

namespace OAI

/-! Matrix Component Bounds. -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace MongeAmpere
variable {n : Type*} [Fintype n]
local notation "Mat" => Matrix n n ℂ

lemma entry_mul_bound {A B : Mat} {a b : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : n) :
    ‖(A*B) i j‖ ≤ (Fintype.card n:ℝ)*a*b := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, ‖A i k*B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : n, a*b := Finset.sum_le_sum (fun k _ => by
      rw [norm_mul]
      exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

lemma trace_entry_bound {A : Mat} {a : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ a) :
    ‖A.trace‖ ≤ (Fintype.card n:ℝ)*a := by
  calc
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, a := Finset.sum_le_sum (fun i _ => hA i i)
    _ = _ := by simp

lemma trace_mul_entry_bound {A B : Mat} {a b : ℝ} (ha : 0 ≤ a)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) :
    ‖(A*B).trace‖ ≤ (Fintype.card n:ℝ)^2*a*b := by
  calc
    _ ≤ (Fintype.card n:ℝ)*((Fintype.card n:ℝ)*a*b) :=
      trace_entry_bound (entry_mul_bound ha hA hB)
    _ = _ := by ring

lemma trace_four_entry_bound {A B C D : Mat} {a b c e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b)
    (hC : ∀ i j, ‖C i j‖ ≤ c) (hD : ∀ i j, ‖D i j‖ ≤ e) :
    ‖(A*B*C*D).trace‖ ≤ (Fintype.card n:ℝ)^4*a*b*c*e := by
  have hn : (0:ℝ) ≤ Fintype.card n := Nat.cast_nonneg _
  have hab := entry_mul_bound ha hA hB
  have habc := entry_mul_bound (mul_nonneg (mul_nonneg hn ha) hb) hab hC
  calc
    _ ≤ (Fintype.card n:ℝ)^2*((Fintype.card n:ℝ)*((Fintype.card n:ℝ)*a*b)*c)*e :=
      trace_mul_entry_bound (by positivity) habc hD
    _ = _ := by ring

lemma contracted_curvature_bound {B : Mat} {R : n → n → Mat} {a r : ℝ}
    (ha : 0 ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ a)
    (hR : ∀ a b i j, ‖R b a i j‖ ≤ r) :
    ‖∑ a, ∑ b, B a b*(B*R b a).trace‖ ≤ (Fintype.card n:ℝ)^4*a^2*r := by
  have ht (i j : n) : ‖(B*R j i).trace‖ ≤ (Fintype.card n:ℝ)^2*a*r :=
    trace_mul_entry_bound ha hB (hR i j)
  calc
    _ ≤ ∑ i, ‖∑ j, B i j*(B*R j i).trace‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖B i j*(B*R j i).trace‖ :=
      Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : n, ∑ _j : n, a*((Fintype.card n:ℝ)^2*a*r) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hB i j) (ht i j) (norm_nonneg _) ha
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end MongeAmpere

end

end OAI
