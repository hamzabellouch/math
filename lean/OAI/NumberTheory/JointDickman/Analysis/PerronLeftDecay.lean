import OAI.NumberTheory.JointDickman.Analysis.ZetaPerronScale
import OAI.NumberTheory.JointDickman.Analysis.LaplaceMovingCutoff

namespace OAI

/-! # Polynomial prefactors in the left-side Perron error -/
namespace JointDickman
open Filter Asymptotics
open scoped Topology

theorem fractional_ratio_power_bound {z C δ : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (C/δ)^z ≤ (1+C)/δ := by
  by_cases h : C/δ ≤ 1
  · calc
      _ ≤ 1 := Real.rpow_le_one (div_nonneg hC hδ.le) h hz
      _ ≤ (1+C)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  · calc
      _ ≤ C/δ := Real.rpow_le_self_of_one_le (le_of_not_ge h) hz1
      _ ≤ (1+C)/δ := div_le_div_of_nonneg_right (by linarith) hδ.le

theorem perronScaleWidth_inverse_bound {A q : ℝ} (hA : 0 < A) (hq : 2 ≤ q) :
    1/perronScaleWidth A q ≤ (2048/A)*q^9 := by
  have hq0 : 0 < q := by linarith
  have hlow : A/2048 ≤ q^9*perronScaleWidth A q := by
    apply (mul_le_mul_iff_right₀ hq0).mp
    calc
      q*(A/2048) = (A/2048)*q := by ring
      _ ≤ q^10*perronScaleWidth A q := perronScaleWidth_mul_lower hA hq
      _ = q*(q^9*perronScaleWidth A q) := by ring
  apply (div_le_iff₀ (perronScaleWidth_pos hA)).mpr
  calc
    1 = (2048/A)*(A/2048) := by field_simp
    _ ≤ (2048/A)*(q^9*perronScaleWidth A q) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    _ = _ := by ring

theorem power9_exp_decay {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun q : ℝ => q^9*Real.exp (-a*q)) =o[atTop] (fun q => q^b) := by
  have h := (isBigO_refl (fun q : ℝ => q^(9:ℝ)) atTop).mul_isLittleO
    (isLittleO_exp_neg_mul_rpow_atTop ha (b-9))
  apply h.congr'
  · exact Eventually.of_forall (fun q => by
      change q^(9:ℝ)*Real.exp (-a*q) = q^9*Real.exp (-a*q)
      rw [Real.rpow_ofNat])
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with q hq
    rw [←Real.rpow_add hq]
    congr 1
    ring

theorem perronScale_left_scalar_decay {z C A : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hC : 0 ≤ C) (hA : 0 < A) (b : ℝ) :
    (fun q : ℝ => (C/perronScaleWidth A q)^z *
      Real.exp (-(q^10*perronScaleWidth A q))) =o[atTop] (fun q => q^b) := by
  apply IsBigO.trans_isLittleO (g := fun q : ℝ => q^9*Real.exp (-(A/2048)*q)) _
    (power9_exp_decay (div_pos hA (by norm_num)) b)
  refine isBigO_iff.mpr ⟨(1+C)*(2048/A),?_⟩
  filter_upwards [eventually_ge_atTop (max 2 A)] with q hq
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hqA : A ≤ q := (le_max_right _ _).trans hq
  have hq0 : 0 < q := by linarith
  have hη := perronScaleWidth_pos hA (q := q)
  have hη1 : perronScaleWidth A q ≤ 1 := by
    apply (perronScaleWidth_upper hA.le hq2).trans
    apply (div_le_iff₀ (by positivity : 0 < 4*q)).mpr
    linarith
  have hp : (C/perronScaleWidth A q)^z ≤ (1+C)*(2048/A)*q^9 := by
    calc
      _ ≤ (1+C)/perronScaleWidth A q := fractional_ratio_power_bound hz hz1 hC hη hη1
      _ = (1+C)*(1/perronScaleWidth A q) := by ring
      _ ≤ (1+C)*((2048/A)*q^9) :=
        mul_le_mul_of_nonneg_left (perronScaleWidth_inverse_bound hA hq2) (by linarith)
      _ = _ := by ring
  have he : Real.exp (-(q^10*perronScaleWidth A q)) ≤ Real.exp (-(A/2048)*q) := by
    apply Real.exp_le_exp.mpr
    have h := perronScaleWidth_mul_lower hA hq2
    nlinarith
  have hl : 0 ≤ (C/perronScaleWidth A q)^z*Real.exp (-(q^10*perronScaleWidth A q)) :=
    mul_nonneg (Real.rpow_nonneg (div_nonneg hC hη.le) _) (Real.exp_pos _).le
  have hr : 0 ≤ q^9*Real.exp (-(A/2048)*q) := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hl,Real.norm_eq_abs,abs_of_nonneg hr]
  calc
    _ ≤ ((1+C)*(2048/A)*q^9)*Real.exp (-(A/2048)*q) :=
      mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

end JointDickman

end OAI
