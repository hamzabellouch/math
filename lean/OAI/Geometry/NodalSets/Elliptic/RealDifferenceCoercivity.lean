import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

namespace Yau
noncomputable section

theorem real_young_coefficient (e B a x y : ℝ) (he : 0 < e) (hB : 0 ≤ B)
    (ha : |a| ≤ B) : -(a*x*y) ≤ e*x^2+(B^2/e)*y^2 := by
  have h0 : -(a*x*y) ≤ B*|x| *|y| := calc
    _ ≤ |a*x*y| := neg_le_abs _
    _ = |a| *|x| *|y| := by rw [abs_mul,abs_mul]
    _ ≤ B*|x| *|y| := mul_le_mul_of_nonneg_right
      (mul_le_mul ha le_rfl (abs_nonneg x) hB) (abs_nonneg y)
  have hs := sq_nonneg (e*|x|-B*|y|)
  have heq : (B^2/e)*e=B^2 := div_mul_cancel₀ _ he.ne'
  have hx := sq_abs x
  have hy := sq_abs y
  have hp := mul_nonneg (sq_nonneg x) (sq_nonneg e)
  have hq := mul_nonneg (sq_nonneg B) (sq_nonneg y)
  apply (mul_le_mul_iff_right₀ he).mp
  nlinarith

theorem real_difference_coercivity (m B : ℝ) (hm : 0 < m) (hB : 0 ≤ B)
    (M N : Fin 4 → Fin 4 → ℝ) (T V R : Fin 4 → ℝ)
    (hM : ∀ a j, |M a j| ≤ B) (hN : ∀ a j, |N a j| ≤ B)
    (hell : m*(∑ j, T j^2) ≤ ∑ a, ∑ j, T a*M a j*T j) :
    (m/2)*(∑ j, T j^2) ≤
      (∑ j, (∑ a, (M a j*T a+N a j*V a))*(T j+2*R j)) +
      (256*B^2/m+4*B)*( (∑ j, V j^2)+(∑ j, R j^2)) := by
  have he : 0 < m/16 := by positivity
  have h1 (a j : Fin 4) : -(2*M a j*T a*R j) ≤
      (m/16)*T a^2+(64*B^2/m)*R j^2 := by
    have h := real_young_coefficient (m/16) B (M a j) (T a) (2*R j) he hB (hM a j)
    convert h using 1 <;> ring
  have h2 (a j : Fin 4) : -(N a j*V a*T j) ≤
      (m/16)*T j^2+(16*B^2/m)*V a^2 := by
    have h := real_young_coefficient (m/16) B (N a j) (T j) (V a) he hB (hN a j)
    convert h using 1 <;> ring
  have h3 (a j : Fin 4) : -(2*N a j*V a*R j) ≤ B*(V a^2+R j^2) := by
    have ha : -(2*N a j*V a*R j) ≤ 2*B*|V a| *|R j| := calc
      _ ≤ |2*N a j*V a*R j| := neg_le_abs _
      _ = 2*|N a j| *|V a| *|R j| := by simp only [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
      _ ≤ 2*B*|V a| *|R j| := by gcongr; exact hN a j
    have hsq := mul_nonneg hB (sq_nonneg (|V a|-|R j|))
    nlinarith [sq_abs (V a),sq_abs (R j)]
  have hs1 := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ h1 a j))
  have hs2 := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ h2 a j))
  have hs3 := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ h3 a j))
  simp only [mul_add,Finset.sum_add_distrib,
    Finset.sum_neg_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs1 hs2 hs3
  simp only [← mul_assoc,← Finset.mul_sum] at hs1 hs2 hs3
  norm_num only [Nat.cast_ofNat] at hs1 hs2 hs3
  have hid : (∑ j, (∑ a, (M a j*T a+N a j*V a))*(T j+2*R j)) =
      (∑ a, ∑ j, T a*M a j*T j) +
      (∑ j, ∑ a, 2*M a j*T a*R j) +
      (∑ j, ∑ a, N a j*V a*T j) +
      (∑ j, ∑ a, 2*N a j*V a*R j) := by
    rw [Finset.sum_comm (f := fun a j ↦ T a*M a j*T j)]
    simp only [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hid]
  have hV : 0 ≤ ∑ j, V j^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hcoef : 0 ≤ 192*B^2/m := by positivity
  have hrest := mul_nonneg hcoef hV
  simp only [div_eq_mul_inv] at hs1 hs2 hrest ⊢
  nlinarith only [hell,hs1,hs2,hs3,hrest]

end
end Yau

end OAI
