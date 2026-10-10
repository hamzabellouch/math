import OAI.Analysis.LipschitzHilbert.Trees.SourceModelDegenerateCases
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

namespace OAI

/-! Finite-support bounded inputs have finite energy, bounded by support area. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert

theorem bounded_supported_input {κ : Type} [Fintype κ]
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) (hg : Measurable g)
    (hbound : ∀ z, ‖g z‖≤1) (F : Set (ℝ×ℝ))
    (hF : MeasurableSet F) (hFfin : (volume.prod volume) F≠∞)
    (hsupport : ∀ z, z∉F → g z=0) :
    MemLp g 2 (volume.prod volume) ∧
      (∫ z, ‖g z‖^2 ∂volume.prod volume)≤(volume.prod volume).real F := by
  have hI : MemLp (F.indicator (fun _ => (1:ℝ))) 2 (volume.prod volume) :=
    memLp_indicator_const 2 hF 1 (Or.inr hFfin)
  have hb (z : ℝ×ℝ) : ‖g z‖≤F.indicator (fun _ => (1:ℝ)) z := by
    by_cases hz : z∈F
    · simpa only [Set.indicator_of_mem hz] using hbound z
    · simp only [Set.indicator_of_notMem hz,hsupport z hz,norm_zero,le_refl]
  have hMem : MemLp g 2 (volume.prod volume) :=
    hI.mono' hg.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  refine ⟨hMem,?_⟩
  have hsq (z : ℝ×ℝ) : ‖g z‖^2≤F.indicator (fun _ => (1:ℝ)) z := by
    by_cases hz : z∈F
    · rw [Set.indicator_of_mem hz]
      nlinarith [hbound z,norm_nonneg (g z)]
    · simp only [Set.indicator_of_notMem hz,hsupport z hz,norm_zero,zero_pow (by decide : 2≠0),le_refl]
  have hle := integral_mono_ae (hMem.integrable_norm_pow (by norm_num : (2:ℕ)≠0))
    ((integrable_indicator_iff hF).2 (integrableOn_const (μ:=volume.prod volume) (C:=(1:ℝ)) hFfin))
    (Filter.Eventually.of_forall hsq)
  simpa only [integral_indicator_const (1:ℝ) hF,smul_eq_mul,mul_one] using hle

theorem reverse_disparity_identity {area support : ℝ} (harea : 0<area) (hsupport : 0<support) :
    area*(area/support)^(-(1/20:ℝ))=
      Real.sqrt (support*area)*(area/support)^(9/20:ℝ) := by
  have hratio : 0<area/support := div_pos harea hsupport
  have he : (9/20:ℝ)=1/2+(-(1/20:ℝ)) := by norm_num
  rw [he,Real.rpow_add hratio,←Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (support*area)*Real.sqrt (area/support)=area := by
    rw [←Real.sqrt_mul (mul_pos hsupport harea).le]
    have hp : support*area*(area/support)=area^2 := by field_simp
    rw [hp,Real.sqrt_sq harea.le]
  rw [←mul_assoc,hsqrt]

end LipschitzHilbert

end

end OAI
