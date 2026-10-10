import Mathlib
import OAI.Computability.VertexCover.Fourier.SourceOccurrences
import OAI.Computability.VertexCover.Analysis.PoincareOne

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Product
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem bounded_memLp (f : X → ℝ) (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)

theorem bounded_integral_norm (f : X → ℝ) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    ‖∫ x, f x ∂μ‖ ≤ C := by
  simpa only [probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)

theorem mean_measurable (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) :
    Measurable (fun x => ∫ y, f x y ∂ν) :=
  hf.stronglyMeasurable.integral_prod_right.measurable

theorem mean_memLp (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hb : ∀ x y, ‖f x y‖ ≤ C) : MemLp (fun x => ∫ y, f x y ∂ν) 2 μ :=
  bounded_memLp μ _ (mean_measurable ν f hf) (fun x => bounded_integral_norm ν _ (hb x))

theorem variance_product (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hb : ∀ x y, ‖f x y‖ ≤ C) :
    variance (Function.uncurry f) (μ.prod ν) =
      (∫ x, variance (f x) ν ∂μ) + variance (fun x => ∫ y, f x y ∂ν) μ := by
  have hp := bounded_memLp (μ.prod ν) _ hf (fun p => hb p.1 p.2)
  have hs : ∀ x, MemLp (f x) 2 ν := fun x =>
    bounded_memLp ν _ (hf.comp (measurable_const.prodMk measurable_id)) (hb x)
  have hm := mean_memLp μ ν f hf hb
  simp_rw [variance_eq_sub (hs _)]
  rw [variance_eq_sub hp, variance_eq_sub hm]
  simp only [Pi.pow_apply]
  dsimp only [Function.uncurry] at hp ⊢
  have hi : Integrable (fun x => ∫ y, (f x y)^2 ∂ν) μ := hp.integrable_sq.integral_prod_left
  have he2 : (∫ p : X × Y, (f p.1 p.2)^2 ∂μ.prod ν) =
      ∫ x, ∫ y, (f x y)^2 ∂ν ∂μ := integral_prod _ hp.integrable_sq
  have he1 : (∫ p : X × Y, f p.1 p.2 ∂μ.prod ν) =
      ∫ x, ∫ y, f x y ∂ν ∂μ := integral_prod _ (hp.integrable (by norm_num))
  rw [integral_sub hi hm.integrable_sq, he2, he1]
  ring

theorem section_variance_integrable (f : X → Y → ℝ)
    (hf : Measurable (Function.uncurry f)) {C : ℝ} (hb : ∀ x y, ‖f x y‖ ≤ C) :
    Integrable (fun x => variance (f x) ν) μ := by
  have hp := bounded_memLp (μ.prod ν) _ hf (fun p => hb p.1 p.2)
  have hs : ∀ x, MemLp (f x) 2 ν := fun x =>
    bounded_memLp ν _ (hf.comp (measurable_const.prodMk measurable_id)) (hb x)
  have hm := mean_memLp μ ν f hf hb
  simp_rw [variance_eq_sub (hs _)]
  exact hp.integrable_sq.integral_prod_left.sub hm.integrable_sq

theorem variance_mean_le (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hb : ∀ x y, ‖f x y‖ ≤ C) :
    variance (fun x => ∫ y, f x y ∂ν) μ ≤ ∫ y, variance (fun x => f x y) μ ∂ν := by
  let g : Y → ℝ := fun y => ∫ x, f x y ∂μ
  let D : X → Y → ℝ := fun x y => f x y - g y
  have hg : Measurable g := mean_measurable μ (fun y x => f x y) (hf.comp measurable_swap)
  have hgb : ∀ y, ‖g y‖ ≤ C := fun y => bounded_integral_norm μ _ (fun x => hb x y)
  have hd : Measurable (Function.uncurry D) := hf.sub (hg.comp measurable_snd)
  have hdb : ∀ x y, ‖D x y‖ ≤ 2*C := fun x y => by
    exact (norm_sub_le _ _).trans (by linarith [hb x y, hgb y])
  have hp := bounded_memLp (μ.prod ν) _ hd (fun p => hdb p.1 p.2)
  have hs : ∀ x, MemLp (D x) 2 ν := fun x =>
    bounded_memLp ν _ (hd.comp (measurable_const.prodMk measurable_id)) (hdb x)
  have hm := mean_memLp μ ν f hf hb
  have hfp := bounded_memLp (μ.prod ν) _ hf (fun p => hb p.1 p.2)
  have hfx : ∀ x, Integrable (f x) ν := fun x =>
    (bounded_memLp ν _ (hf.comp (measurable_const.prodMk measurable_id)) (hb x)).integrable (by norm_num)
  have hgi := (bounded_memLp ν g hg hgb).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hei : ∫ y, g y ∂ν = ∫ x, ∫ y, f x y ∂ν ∂μ := by
    exact (integral_integral_swap (hfp.integrable (by norm_num))).symm
  have he : ∀ x, (∫ y, f x y ∂ν) - ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, D x y ∂ν := by
    intro x
    dsimp only [D]
    rw [integral_sub (hfx x) hgi, hei]
  rw [variance_eq_integral hm.aemeasurable]
  simp_rw [he]
  calc
    _ ≤ ∫ x, ∫ y, (D x y)^2 ∂ν ∂μ := by
      apply integral_mono
      · exact (mean_memLp μ ν D hd hdb).integrable_sq
      · exact hp.integrable_sq.integral_prod_left
      · intro x
        simpa only [probReal_univ, one_mul] using Cube.sq_integral_le_measure_mul ν (hs x)
    _ = ∫ y, ∫ x, (D x y)^2 ∂μ ∂ν := integral_integral_swap hp.integrable_sq
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y =>
        (variance_eq_integral (hf.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm)

theorem variance_product_le (f : X → Y → ℝ) (hf : Measurable (Function.uncurry f)) {C : ℝ}
    (hb : ∀ x y, ‖f x y‖ ≤ C) :
    variance (Function.uncurry f) (μ.prod ν) ≤
      (∫ x, variance (f x) ν ∂μ) + ∫ y, variance (fun x => f x y) μ ∂ν := by
  rw [variance_product μ ν f hf hb]
  exact add_le_add le_rfl (variance_mean_le μ ν f hf hb)

end VertexCover.Product


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
