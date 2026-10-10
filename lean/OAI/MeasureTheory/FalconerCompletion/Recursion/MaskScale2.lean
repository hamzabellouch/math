import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Recursion.MaskScale
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Filter Real
open scoped Topology

noncomputable def sourceMaskScaleND (l : ℕ) (R σ : ℝ) : ℝ :=
  max 1 ((2:ℝ)^l*R^(-50*σ))

noncomputable def sourceMaskRadiusND (d l : ℕ) (R σ : ℝ) : ℝ :=
  (sourceMaskScaleND l R σ)⁻¹/(100*(d+1)^2)

noncomputable def sourceTestWidthND (J i n : ℕ) (R σ : ℝ) : ℝ :=
  (2-(i:ℝ)/J)*((2:ℝ)^n)⁻¹*R^(500*σ)

lemma sourceMaskScaleND_one_le (l : ℕ) (R σ : ℝ) : 1 ≤ sourceMaskScaleND l R σ := le_max_left _ _

lemma sourceMaskScaleND_pos (l : ℕ) (R σ : ℝ) : 0<sourceMaskScaleND l R σ :=
  zero_lt_one.trans_le (sourceMaskScaleND_one_le l R σ)

lemma sourceMaskRadiusND_pos (d l : ℕ) (R σ : ℝ) : 0<sourceMaskRadiusND d l R σ :=
  div_pos (inv_pos.mpr (sourceMaskScaleND_pos l R σ)) (by positivity)

lemma sourceMaskScaleND_mono {l L : ℕ} (h : l ≤ L) {R σ : ℝ} (hR : 0 ≤ R) :
    sourceMaskScaleND l R σ ≤ sourceMaskScaleND L R σ := by
  apply max_le_max_left
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) h) (Real.rpow_nonneg hR _)

lemma sourceMaskScaleND_inv_depth {g p : ℕ} (hgp : g ≤ p) {R σ : ℝ} (hR : 0<R) :
    ((2:ℝ)^g)⁻¹*(sourceMaskScaleND (p-g) R σ)⁻¹ ≤ ((2:ℝ)^p)⁻¹*R^(50*σ) := by
  have hpos : 0<(2:ℝ)^(p-g)*R^(-50*σ) := by positivity
  have hh := inv_anti₀ hpos (le_max_right (1:ℝ) ((2:ℝ)^(p-g)*R^(-50*σ)))
  apply (mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ ((2:ℝ)^g)⁻¹)).trans_eq
  rw [mul_inv_rev,show -50*σ=-(50*σ) by ring,Real.rpow_neg hR.le,inv_inv]
  calc
    _ = (((2:ℝ)^g)*((2:ℝ)^(p-g)))⁻¹*R^(50*σ) := by rw [mul_inv_rev]; ring
    _ = _ := by rw [← pow_add,Nat.add_sub_of_le hgp]

lemma sourceTestWidthND_gap {J : ℕ} (hJ : 0<J) (i n : ℕ) (R σ : ℝ) :
    sourceTestWidthND J i n R σ-sourceTestWidthND J (i+1) n R σ =
      (J:ℝ)⁻¹*((2:ℝ)^n)⁻¹*R^(500*σ) := by
  unfold sourceTestWidthND
  push_cast
  have hJ' : (J:ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  field_simp
  ring

lemma source_mask_width_gapND {d g p J i : ℕ} {R σ : ℝ}
    (hgp : g ≤ p) (hJ : 0<J) (hR : 0<R) (hlarge : (J:ℝ) ≤ R^(450*σ)) :
    sourceTestWidthND J (i+1) p R σ+
      40*(d+1)^2/(2:ℝ)^g*sourceMaskRadiusND d (p-g) R σ ≤
      sourceTestWidthND J i p R σ := by
  have hD := sourceMaskScaleND_inv_depth hgp hR (σ := σ)
  have hJn : (0:ℝ)<J := by exact_mod_cast hJ
  have hpow : R^(50*σ) ≤ (J:ℝ)⁻¹*R^(500*σ) := by
    calc
      _ ≤ ((J:ℝ)⁻¹*R^(450*σ))*R^(50*σ) := by
        apply le_mul_of_one_le_left (Real.rpow_nonneg hR.le _)
        exact (one_le_inv_mul₀ hJn).mpr hlarge
      _ = _ := by rw [mul_assoc,← Real.rpow_add hR]; congr 2; ring
  have hpert : 40*(d+1)^2/(2:ℝ)^g*sourceMaskRadiusND d (p-g) R σ ≤
      (J:ℝ)⁻¹*((2:ℝ)^p)⁻¹*R^(500*σ) := by
    unfold sourceMaskRadiusND
    calc
      _ = (2/5:ℝ)*(((2:ℝ)^g)⁻¹*(sourceMaskScaleND (p-g) R σ)⁻¹) := by field_simp; ring
      _ ≤ (2/5:ℝ)*(((2:ℝ)^p)⁻¹*R^(50*σ)) := mul_le_mul_of_nonneg_left hD (by norm_num)
      _ ≤ ((2:ℝ)^p)⁻¹*R^(50*σ) := mul_le_of_le_one_left (by positivity) (by norm_num)
      _ ≤ _ := by simpa only [mul_left_comm,mul_assoc] using mul_le_mul_of_nonneg_left hpow (by positivity : (0:ℝ) ≤ ((2:ℝ)^p)⁻¹)
  have he := sourceTestWidthND_gap hJ i p R σ
  linarith

theorem source_mask_width_gap_eventuallyND {σ : ℝ} (hσ : 0<σ) (d J : ℕ) (hJ : 0<J) :
    ∀ᶠ R : ℝ in atTop, ∀ g p i : ℕ, g ≤ p →
      sourceTestWidthND J (i+1) p R σ+
        40*(d+1)^2/(2:ℝ)^g*sourceMaskRadiusND d (p-g) R σ ≤
        sourceTestWidthND J i p R σ := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (by positivity : (0:ℝ)<450*σ)).eventually_ge_atTop (J:ℝ)] with R hR hlarge
  intro g p i hgp
  exact source_mask_width_gapND hgp hJ hR hlarge

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
