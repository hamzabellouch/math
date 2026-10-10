import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! The fixed divisor cutoff preserves the hybrid sieve range when the
frequency length is at most the three-fifths power of the coefficient length. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma stopped_divisor_cutoff_geometry {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ b B : ℝ, X^κ ≤ b → B ≤ b^(3/5:ℝ) →
      1 ≤ b ∧ 65536 ≤ b/b^(1/8:ℝ) ∧
        8*B ≤ (b/b^(1/8:ℝ))^(3/4:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0 < κ*(7/8) by positivity)).eventually_ge_atTop 65536,
    (tendsto_rpow_atTop (show 0 < κ*(9/160) by positivity)).eventually_ge_atTop 8]
    with X hX hsize hgap
  intro b B hb hB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hb1 : 1 ≤ b := (Real.one_le_rpow hX hκ.le).trans hb
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hquot : b/b^(1/8:ℝ) = b^(7/8:ℝ) := by
    rw [div_eq_mul_inv,←Real.rpow_neg hbp.le]
    nth_rw 1 [←Real.rpow_one b]
    rw [←Real.rpow_add hbp]
    norm_num
  have hsize' : 65536 ≤ b^(7/8:ℝ) := by
    apply hsize.trans
    rw [Real.rpow_mul hXp.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hb (by norm_num)
  have hgap' : 8 ≤ b^(9/160:ℝ) := by
    apply hgap.trans
    rw [Real.rpow_mul hXp.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hb (by norm_num)
  refine ⟨hb1,by rwa [hquot],?_⟩
  calc
    8*B ≤ 8*b^(3/5:ℝ) := mul_le_mul_of_nonneg_left hB (by norm_num)
    _ ≤ b^(9/160:ℝ)*b^(3/5:ℝ) :=
      mul_le_mul_of_nonneg_right hgap' (Real.rpow_nonneg hbp.le _)
    _ = (b/b^(1/8:ℝ))^(3/4:ℝ) := by
      rw [hquot,←Real.rpow_add hbp,←Real.rpow_mul hbp.le]
      norm_num

end CubicFirstMoment

end

end OAI
