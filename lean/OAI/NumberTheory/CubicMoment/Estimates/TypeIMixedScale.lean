import OAI.NumberTheory.CubicMoment.Estimates.TypeIMixedFull
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! The fixed product-support dilation is absorbed by the actual Type-I
margin. The corrected-square normalization is an exact power identity. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma typeIMixed_scale_identity {A L : ℝ} (hA : 0 < A) (hL : 0 < L) (η : ℝ) :
    A^(-1/6:ℝ)*L^(5/6:ℝ)*(L*A)^(5/6-η) =
      A^(2/3:ℝ)*L^(5/3:ℝ)*(L*A)^(-η) := by
  rw [Real.mul_rpow hL.le hA.le,Real.mul_rpow hL.le hA.le,
    show (5/6-η:ℝ) = (5/6)+(-η) by ring,
    Real.rpow_add hL,Real.rpow_add hA]
  have ha : A^(-1/6:ℝ)*A^(5/6:ℝ) = A^(2/3:ℝ) := by
    rw [←Real.rpow_add hA]
    norm_num
  have hl : L^(5/6:ℝ)*L^(5/6:ℝ) = L^(5/3:ℝ) := by
    rw [←Real.rpow_add hL]
    norm_num
  calc
    _ = (A^(-1/6:ℝ)*A^(5/6:ℝ))*(L^(5/6:ℝ)*L^(5/6:ℝ))*(L^(-η)*A^(-η)) := by ring
    _ = _ := by rw [ha,hl]

lemma eventually_typeIMixed_dilation (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ A : ℝ, L^(99/100:ℝ) ≤ A → C*L ≤ (L*A)^(51/100:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_const_mul_rpow_le (by norm_num : (1:ℝ) < 101/100) C] with L hL hC
  intro A hA
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hbase : L^(199/100:ℝ) ≤ L*A := by
    calc
      _ = L^(1:ℝ)*L^(99/100:ℝ) := by rw [←Real.rpow_add hLp]; norm_num
      _ ≤ _ := by rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hA hLp.le
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hLp.le (199/100)) hbase
    (by norm_num : (0:ℝ) ≤ 51/100)
  rw [←Real.rpow_mul hLp.le] at hpow
  calc
    C*L = C*L^(1:ℝ) := by rw [Real.rpow_one]
    _ ≤ L^(101/100:ℝ) := hC
    _ ≤ L^((199/100:ℝ)*(51/100)) := Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
    _ ≤ _ := hpow

end CubicFirstMoment

end

end OAI
