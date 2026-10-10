import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

section
open scoped BigOperators
namespace MinUncut.FiniteGaussian

lemma normalized_test_bound {G E X Y : ℝ} (hG : 0 < G) (hE : 0 ≤ E)
    (hX : 0 ≤ X) (hXG : X ≤ G) (hY : 0 ≤ Y) (hYE : Y ≤ E) :
    |(X+Y)/(G+E)-X/G| ≤ E/(G+E) := by
  have hGE : 0 < G+E := by linarith
  have he : (X+Y)/(G+E)-X/G=(G*Y-E*X)/(G*(G+E)) := by
    field_simp
    ring
  have he' : E/(G+E)=(E*G)/(G*(G+E)) := by
    field_simp
  rw [he,he',abs_div,abs_of_pos (mul_pos hG hGE),div_le_div_iff_of_pos_right (mul_pos hG hGE)]
  apply abs_le.mpr
  constructor
  · nlinarith [mul_nonneg hG.le hY,mul_nonneg hE (sub_nonneg.mpr hXG)]
  · nlinarith [mul_nonneg hE hX,mul_nonneg hG.le (sub_nonneg.mpr hYE)]

lemma finite_normalized_test_bound {ι : Type*} [Fintype ι] (q g F : ι → ℝ)
    (hg : ∀ i, 0 ≤ g i) (hqg : ∀ i, g i ≤ q i)
    (hG : 0 < ∑ i, g i) (hF : ∀ i, 0 ≤ F i ∧ F i ≤ 1) :
    |(∑ i, q i*F i)/(∑ i, q i)-(∑ i, g i*F i)/(∑ i, g i)| ≤
      ((∑ i, q i)-(∑ i, g i))/(∑ i, q i) := by
  have residual : 0 ≤ ∑ i, (q i-g i) :=
    Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hqg i))
  have hx : 0 ≤ ∑ i, g i*F i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hg i) (hF i).1)
  have hxg : (∑ i, g i*F i) ≤ ∑ i, g i :=
    Finset.sum_le_sum (fun i _ => by nlinarith [mul_nonneg (hg i) (sub_nonneg.mpr (hF i).2)])
  have hy : 0 ≤ ∑ i, (q i-g i)*F i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sub_nonneg.mpr (hqg i)) (hF i).1)
  have hye : (∑ i, (q i-g i)*F i) ≤ ∑ i, (q i-g i) :=
    Finset.sum_le_sum (fun i _ => by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hqg i)) (sub_nonneg.mpr (hF i).2)])
  have hh := normalized_test_bound hG residual hx hxg hy hye
  have he : (∑ i, g i*F i)+(∑ i, (q i-g i)*F i)=∑ i, q i*F i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he' : (∑ i, g i)+(∑ i, (q i-g i))=∑ i, q i := by
    rw [Finset.sum_sub_distrib]; ring
  rw [he,he'] at hh
  simpa only [Finset.sum_sub_distrib] using hh

end MinUncut.FiniteGaussian

end
section
open scoped BigOperators
namespace MinUncut.FiniteGaussian

lemma product_residual_bound {G Q : ℝ} (hG : 1 ≤ G) (hGQ : G ≤ Q) (d : ℕ) :
    (Q^d-G^d)/Q^d ≤ (d:ℝ)*(Q-G) := by
  have hG0 : 0 < G := by linarith
  have hQ : 0 < Q := hG0.trans_le hGQ
  have hratio : 0 ≤ G/Q := by positivity
  have hbern := one_add_mul_sub_le_pow (by linarith : (-1:ℝ) ≤ G/Q) d
  have he : (Q^d-G^d)/Q^d=1-(G/Q)^d := by
    rw [div_pow,sub_div,div_self (pow_ne_zero _ hQ.ne')]
  have hr : (Q-G)/Q ≤ Q-G := div_le_self (sub_nonneg.mpr hGQ) (hG.trans hGQ)
  have hh : 1-(G/Q)^d ≤ (d:ℝ)*((Q-G)/Q) := by
    rw [sub_div,div_self hQ.ne']
    nlinarith
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg d))

lemma finite_product_test_bound {α : Type*} [Fintype α] (q g : α → ℝ)
    (hg : ∀ a, 0 ≤ g a) (hqg : ∀ a, g a ≤ q a)
    (hG : 1 ≤ ∑ a, g a) (d : ℕ) (F : (Fin d → α) → ℝ)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    |(∑ x, (∏ i, q (x i))*F x)/(∑ a, q a)^d-
      (∑ x, (∏ i, g (x i))*F x)/(∑ a, g a)^d| ≤
      (d:ℝ)*((∑ a, q a)-(∑ a, g a)) := by
  have hg0 : 0 < ∑ a, g a := by linarith
  have hq0 (a : α) : 0 ≤ q a := (hg a).trans (hqg a)
  have hgprod (x : Fin d → α) : 0 ≤ ∏ i, g (x i) :=
    Finset.prod_nonneg (fun i _ => hg (x i))
  have hprod (x : Fin d → α) : (∏ i, g (x i)) ≤ ∏ i, q (x i) :=
    Finset.prod_le_prod₀ (fun index _ => hg (x index)) (fun index _ => hqg (x index))
  have hsum (w : α → ℝ) : (∑ x : Fin d → α, ∏ i, w (x i))=(∑ a, w a)^d :=
    (Fintype.sum_pow w d).symm
  have htotal : 0 < ∑ x : Fin d → α, ∏ i, g (x i) := by
    rw [hsum]; exact pow_pos hg0 d
  have hh := finite_normalized_test_bound (fun x : Fin d → α => ∏ i, q (x i))
    (fun x => ∏ i, g (x i)) F hgprod hprod htotal hF
  rw [hsum,hsum] at hh
  exact hh.trans (product_residual_bound hG (Finset.sum_le_sum (fun a _ => hqg a)) d)

end MinUncut.FiniteGaussian

end

end OAI
