import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Finite-fibre integration preserves uniform integrability -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem uniformIntegrable_restrict {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) (s : Set X) :
    UniformIntegrable f 1 (μ.restrict s) := by
  obtain ⟨C,hC⟩ := hf.2
  exact ⟨hf.1.restrict s,C,fun n =>
    (eLpNorm_mono_measure (f n) Measure.restrict_le_self).trans (hC n)⟩

theorem uniformIntegrable_comp {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) (a : ℕ → ℕ) :
    UniformIntegrable (fun n => f (a n)) 1 μ := by
  obtain ⟨C,hC⟩ := hf.2
  exact ⟨hf.1.comp a,C,fun n => hC (a n)⟩

theorem eLpNorm_integral_le {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => ∫ y, f (x,y) ∂ν) 1 μ ≤ eLpNorm f 1 (μ.prod ν) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,lintegral_prod _ hf.enorm.aemeasurable]
  exact lintegral_mono (fun x => enorm_integral_le_lintegral_enorm _)

theorem uniformIntegrable_integral {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [IsFiniteMeasure ν] {f : ℕ → X × Y → ℝ}
    (hf : ∀ n, Measurable (f n)) (hui : UniformIntegrable f 1 (μ.prod ν)) :
    UniformIntegrable (fun n x => ∫ y, f n (x,y) ∂ν) 1 μ := by
  constructor
  · apply unifIntegrable_iff'.mpr
    intro ε hε
    obtain ⟨δ,hδ,hsmall⟩ := unifIntegrable_iff'.mp hui.1 ε hε
    let B : ℝ≥0∞ := ν univ+1
    have hB : B ≠ 0 := by simp [B]
    have hBtop : B ≠ ∞ := by simp [B,measure_ne_top]
    refine ⟨δ/B,ENNReal.div_pos hδ.ne' hBtop,?_⟩
    intro n s hs hμs
    have hvol : (μ.prod ν) (s ×ˢ univ) ≤ δ := by
      rw [Measure.prod_prod]
      calc
        μ s*ν univ ≤ (δ/B)*B := mul_le_mul' hμs (le_self_add)
        _ = δ := ENNReal.div_mul_cancel hB hBtop
    calc
      _ ≤ eLpNorm (f n) 1 ((μ.restrict s).prod ν) := eLpNorm_integral_le (hf n)
      _ = eLpNorm (f n) 1 ((μ.prod ν).restrict (s ×ˢ univ)) := by
        rw [← Measure.prod_restrict,Measure.restrict_univ]
      _ ≤ ε := hsmall n (s ×ˢ univ) (hs.prod MeasurableSet.univ) hvol
  · obtain ⟨C,hC⟩ := hui.2
    exact ⟨C,fun n => (eLpNorm_integral_le (hf n)).trans (hC n)⟩

end BoltzmannNonuniqueness.Compactness

end

end OAI
