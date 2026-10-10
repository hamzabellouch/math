import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianDensityError

namespace OAI

section
open scoped BigOperators
namespace MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
lemma finite_product_test_bound_general {ι α : Type*} [Fintype ι] [Fintype α] (q g : α → ℝ)
    (hg : ∀ a, 0 ≤ g a) (hqg : ∀ a, g a ≤ q a)
    (hG : 1 ≤ ∑ a, g a) (F : (ι → α) → ℝ)
    (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    |(∑ x, (∏ i, q (x i))*F x)/(∑ a, q a)^(Fintype.card ι)-
      (∑ x, (∏ i, g (x i))*F x)/(∑ a, g a)^(Fintype.card ι)| ≤
      (Fintype.card ι:ℝ)*((∑ a, q a)-(∑ a, g a)) := by
  classical
  have hg0 : 0 < ∑ a, g a := by linarith
  have hq0 (a : α) : 0 ≤ q a := (hg a).trans (hqg a)
  have hgprod (x : ι → α) : 0 ≤ ∏ i, g (x i) :=
    Finset.prod_nonneg (fun i _ => hg (x i))
  have hprod (x : ι → α) : (∏ i, g (x i)) ≤ ∏ i, q (x i) :=
    Finset.prod_le_prod₀ (fun index _ => hg (x index)) (fun index _ => hqg (x index))
  have hsum (w : α → ℝ) : (∑ x : ι → α, ∏ i, w (x i))=(∑ a, w a)^(Fintype.card ι) :=
    by simpa only [Finset.prod_const,Finset.card_univ] using (Fintype.prod_sum (fun _ : ι => w)).symm
  have htotal : 0 < ∑ x : ι → α, ∏ i, g (x i) := by
    rw [hsum]; exact pow_pos hg0 (Fintype.card ι)
  have hh := finite_normalized_test_bound (fun x : ι → α => ∏ i, q (x i))
    (fun x => ∏ i, g (x i)) F hgprod hprod htotal hF
  rw [hsum,hsum] at hh
  exact hh.trans (product_residual_bound hG (Finset.sum_le_sum (fun a _ => hqg a)) (Fintype.card ι))

end MinUncut.FiniteGaussian

end
section
open scoped BigOperators
namespace MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
lemma grid_product_bound_general {ι : Type*} [Fintype ι] {T : ℚ} (hT : 1 ≤ T) {L : ℕ} (hL : 0 < L)
    (r : ℕ) (F : (ι → Fin L) → ℝ) (hF : ∀ x, 0 ≤ F x ∧ F x ≤ 1) :
    |(∑ x, (∏ i, qCell r T L (x i))*F x)/(qIntegral r (-T) T:ℝ)^(Fintype.card ι)-
      (∑ x, (∏ i, gCell T L (x i))*F x)/(gIntegral (-T) T)^(Fintype.card ι)| ≤
        2*(Fintype.card ι)*(T:ℝ)*error r ((T:ℝ)^2/2) := by
  have hT0 : 0 < T := by linarith
  have hT' : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hb := finite_product_test_bound_general (qCell r T L) (gCell T L)
    (gCell_nonneg hT0 hL) (gCell_le_qCell hT0 hL r)
    (by rw [sum_gCell T hL]; exact (gIntegral_large hT').le) F hF
  rw [sum_qCell r T hL,sum_gCell T hL] at hb
  exact hb.trans (by
    have hh := mul_le_mul_of_nonneg_left (residual_bounds hT0.le r).2 (Nat.cast_nonneg (α := ℝ) (Fintype.card ι))
    nlinarith)

end MinUncut.FiniteGaussian

end

end OAI
