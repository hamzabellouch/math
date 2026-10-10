import OAI.MeasureTheory.Falconer.Radial.WeakRadialLocalBudget

namespace OAI

/-! # The profile increments telescope without a factor for initial cells -/

namespace Falconer
open scoped ENNReal BigOperators

theorem profile_loss_product {R : ℝ} (hR : 0 < R) (m : ℕ → ℝ) (A β : ℝ) (J : ℕ) :
    (∏ j ∈ Finset.range J, R^(A-β*(m (j+1)-m j))) =
      R^((J:ℝ)*A-β*(m J-m 0)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.prod_range_succ,ih,← Real.rpow_add hR]
    congr 1
    push_cast
    ring

theorem profile_loss_product_ennreal {R : ℝ} (hR : 0 < R) (m : ℕ → ℝ) (A β : ℝ) (J : ℕ) :
    (∏ j ∈ Finset.range J, ENNReal.ofReal (R^(A-β*(m (j+1)-m j)))) =
      ENNReal.ofReal (R^((J:ℝ)*A-β*(m J-m 0))) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.prod_range_succ,ih,← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
      ← Real.rpow_add hR]
    congr 2
    push_cast
    ring

theorem profile_loss_product_bound {R : ℝ} (hR : 1 ≤ R) (m : ℕ → ℝ)
    {A β s b ℓ : ℝ} (hβ : 0 ≤ β) (J : ℕ)
    (hmJ : s ≤ m J) (hm0 : m 0 ≤ b) (hgap : (J:ℝ)*A-β*(s-b) ≤ -ℓ) :
    (∏ j ∈ Finset.range J, ENNReal.ofReal (R^(A-β*(m (j+1)-m j)))) ≤
      ENNReal.ofReal (R^(-ℓ)) := by
  rw [profile_loss_product_ennreal (lt_of_lt_of_le zero_lt_one hR)]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hh := mul_le_mul_of_nonneg_left (sub_le_sub hmJ hm0) hβ
  linarith

theorem density_profile_factor {R : ℝ} (hR : 0 < R) (a b β u v : ℝ) :
    (ENNReal.ofReal (R^(-a)))⁻¹*ENNReal.ofReal (R^(b-β*(v-u))) =
      ENNReal.ofReal (R^(a+b-β*(v-u))) := by
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hR _),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg hR.le _)),
    ← Real.rpow_neg hR.le,neg_neg,← Real.rpow_add hR]
  congr 2
  ring

theorem profile_fraction_eq {R : ℝ} (hR : 0 < R) (e β u v : ℝ) :
    R^e/(R^(v-u))^β = R^(e-β*(v-u)) := by
  rw [← Real.rpow_mul hR.le,← Real.rpow_sub hR]
  congr 1
  ring

theorem density_profile_product_bound {R : ℝ} (hR : 1 ≤ R)
    (m : ℕ → ℝ) {a b β s t ℓ : ℝ} (hβ : 0 ≤ β) (J : ℕ)
    (hmJ : s ≤ m J) (hm0 : m 0 ≤ t)
    (hgap : (J:ℝ)*(a+b)-β*(s-t) ≤ -ℓ) :
    (∏ j ∈ Finset.range J,
      (ENNReal.ofReal (R^(-a)))⁻¹*ENNReal.ofReal (R^(b-β*(m (j+1)-m j)))) ≤
      ENNReal.ofReal (R^(-ℓ)) := by
  simp_rw [density_profile_factor (lt_of_lt_of_le zero_lt_one hR)]
  exact profile_loss_product_bound hR m hβ J hmJ hm0 hgap

end Falconer

end OAI
