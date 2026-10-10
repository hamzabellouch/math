import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

namespace OAI

/-! # Square-integrable averages over probability fibers

These estimates justify the whole-fiber averages in the inverse coupling.
The outer measure may be finite without being normalized.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PolycyclicRecognition

variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Normalize the restriction to a region of positive finite mass. -/
def normalizedRestriction (m : Measure Y) (B : Set Y) : Measure Y :=
  (m B)⁻¹ • m.restrict B

/-- A positive finite region defines a probability measure on its whole
volume, rather than on a chosen representative point. -/
theorem normalizedRestriction_probability (m : Measure Y) {B : Set Y}
    (hB0 : m B ≠ 0) (hBtop : m B ≠ ∞) :
    IsProbabilityMeasure (normalizedRestriction m B) := by
  constructor
  rw [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel hB0 hBtop]

omit [NormedSpace ℝ W] in
/-- Normalizing one finite fiber preserves square integrability. -/
theorem memLp_normalizedRestriction_product (ν : Measure X) [SFinite ν]
    (m : Measure Y) [SFinite m] {B : Set Y} (hB0 : m B ≠ 0)
    {f : X × Y → W} (hf : MemLp f 2 (ν.prod (m.restrict B))) :
    MemLp f 2 (ν.prod (normalizedRestriction m B)) := by
  rw [normalizedRestriction, Measure.prod_smul_right]
  exact hf.smul_measure (ENNReal.inv_ne_top.mpr hB0)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Normalizing both averaging variables contributes exactly the inverse
square of the region's mass. -/
theorem lintegral_normalizedRestriction_two (ν : Measure X) (m : Measure Y)
    {B : Set Y} (hB0 : m B ≠ 0) (f : X → Y → Y → ℝ≥0∞) :
    (∫⁻ x, ∫⁻ y, ∫⁻ z, f x y z ∂(normalizedRestriction m B)
      ∂(normalizedRestriction m B) ∂ν) =
      ((m B)⁻¹) ^ 2 * ∫⁻ x, ∫⁻ y in B, ∫⁻ z in B, f x y z ∂m ∂m ∂ν := by
  simp_rw [normalizedRestriction, lintegral_smul_measure, smul_eq_mul,
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hB0)]
  rw [pow_two]
  ac_rfl

/-- Jensen's square estimate for the norm of a Bochner average. -/
theorem norm_integral_sq_le (β : Measure Y) [IsProbabilityMeasure β]
    {f : Y → W} (hf : MemLp f 2 β) :
    ‖∫ y, f y ∂β‖ ^ 2 ≤ ∫ y, ‖f y‖ ^ 2 ∂β := by
  have hfi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hj := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    (continuous_pow 2).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun y => norm_nonneg (f y)) hfi.norm hsq
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm f) 2).trans hj

/-- The nonnegative extended-real form of the square estimate, used with
Tonelli when comparing whole fibers. -/
theorem enorm_integral_sq_le (β : Measure Y) [IsProbabilityMeasure β]
    {f : Y → W} (hf : MemLp f 2 β) :
    ‖∫ y, f y ∂β‖ₑ ^ 2 ≤ ∫⁻ y, ‖f y‖ₑ ^ 2 ∂β := by
  have h := ENNReal.ofReal_le_ofReal (norm_integral_sq_le β hf)
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  rw [ofReal_integral_eq_lintegral_ofReal hsq
    (Filter.Eventually.of_forall fun y => sq_nonneg ‖f y‖)] at h
  simpa only [ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm] using h

/-- A square-integrable function on a finite product has square-integrable
fiber averages, with the expected contraction of the squared norm. -/
theorem memLp_fiberAverage (ν : Measure X) [IsFiniteMeasure ν]
    (β : Measure Y) [IsProbabilityMeasure β]
    {f : X × Y → W} (hf : MemLp f 2 (ν.prod β)) :
    MemLp (fun x => ∫ y, f (x, y) ∂β) 2 ν ∧
      (∫ x, ‖∫ y, f (x, y) ∂β‖ ^ 2 ∂ν) ≤
        ∫ q, ‖f q‖ ^ 2 ∂(ν.prod β) := by
  have hmeas := hf.aestronglyMeasurable.integral_prod_right'
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hsect : ∀ᵐ x ∂ν, MemLp (fun y => f (x, y)) 2 β := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left,
      (integrable_prod_iff hsq.aestronglyMeasurable).mp hsq |>.1] with x hx hix
    exact (memLp_two_iff_integrable_sq_norm hx).mpr hix
  have hbound : ∀ᵐ x ∂ν,
      ‖∫ y, f (x, y) ∂β‖ ^ 2 ≤ ∫ y, ‖f (x, y)‖ ^ 2 ∂β :=
    hsect.mono fun _ hx => norm_integral_sq_le β hx
  have hint : Integrable (fun x => ‖∫ y, f (x, y) ∂β‖ ^ 2) ν := by
    apply hsq.integral_prod_left.mono'
      (hmeas.norm.pow 2)
    filter_upwards [hbound] with x hx
    change |‖∫ y, f (x, y) ∂β‖ ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hx
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).mpr hint, ?_⟩
  rw [integral_prod _ hsq]
  exact integral_mono_ae hint hsq.integral_prod_left hbound

/-- Comparing two averages by the mean squared difference over the whole
product fiber. This is the estimate used before enlarging translated balls. -/
theorem norm_sub_integral_sq_le [CompleteSpace W] (β : Measure Y) [IsProbabilityMeasure β]
    {f g : Y → W} (hf : MemLp f 2 β) (hg : MemLp g 2 β) :
    ‖(∫ y, f y ∂β) - ∫ y, g y ∂β‖ ^ 2 ≤
      ∫ y, ∫ z, ‖f y - g z‖ ^ 2 ∂β ∂β := by
  have hfg : MemLp (fun q : Y × Y => f q.1 - g q.2) 2 (β.prod β) :=
    (hf.comp_fst β).sub (hg.comp_snd β)
  have hi := norm_integral_sq_le (β.prod β) hfg
  have hfi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgi := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hsq := (memLp_two_iff_integrable_sq_norm hfg.aestronglyMeasurable).mp hfg
  rw [integral_prod _ (hfg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))] at hi
  have hev : (∫ y, ∫ z, f y - g z ∂β ∂β) = (∫ y, f y ∂β) - ∫ z, g z ∂β := by
    have hin (y : Y) : (∫ z, f y - g z ∂β) = f y - ∫ z, g z ∂β := by
      rw [integral_sub (integrable_const (f y)) hgi, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    simp_rw [hin]
    rw [integral_sub hfi (integrable_const (∫ z, g z ∂β)), integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hev, integral_prod _ hsq] at hi
  exact hi

/-- Extended-real version of the whole-product oscillation estimate. -/
theorem enorm_sub_integral_sq_le [CompleteSpace W]
    (β : Measure Y) [IsProbabilityMeasure β]
    {f g : Y → W} (hf : MemLp f 2 β) (hg : MemLp g 2 β) :
    ‖(∫ y, f y ∂β) - ∫ y, g y ∂β‖ₑ ^ 2 ≤
      ∫⁻ y, ∫⁻ z, ‖f y - g z‖ₑ ^ 2 ∂β ∂β := by
  have hfg : MemLp (fun q : Y × Y => f q.1 - g q.2) 2 (β.prod β) :=
    (hf.comp_fst β).sub (hg.comp_snd β)
  have hi := enorm_integral_sq_le (β.prod β) hfg
  have hfi := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgi := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [integral_prod _ (hfg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))] at hi
  have hev : (∫ y, ∫ z, f y - g z ∂β ∂β) = (∫ y, f y ∂β) - ∫ z, g z ∂β := by
    have hin (y : Y) : (∫ z, f y - g z ∂β) = f y - ∫ z, g z ∂β := by
      rw [integral_sub (integrable_const (f y)) hgi, integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    simp_rw [hin]
    rw [integral_sub hfi (integrable_const (∫ z, g z ∂β)), integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  rw [hev, lintegral_prod _ (hfg.aestronglyMeasurable.enorm.pow_const 2)] at hi
  exact hi

/-- The integrated error of fiber averages is controlled by the integrated
oscillation over the full product of the fibers. -/
theorem fiber_average_error_lintegral_le [CompleteSpace W]
    (ν : Measure X) [IsFiniteMeasure ν] (β : Measure Y) [IsProbabilityMeasure β]
    {f g : X × Y → W} (hf : MemLp f 2 (ν.prod β)) (hg : MemLp g 2 (ν.prod β)) :
    (∫⁻ x, ‖∫ y, f (x, y) - g (x, y) ∂β‖ₑ ^ 2 ∂ν) ≤
      ∫⁻ x, ∫⁻ y, ∫⁻ z, ‖f (x, y) - g (x, z)‖ₑ ^ 2 ∂β ∂β ∂ν := by
  have hfsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hgsq := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  apply lintegral_mono_ae
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hg.aestronglyMeasurable.prodMk_left,
    (integrable_prod_iff hfsq.aestronglyMeasurable).mp hfsq |>.1,
    (integrable_prod_iff hgsq.aestronglyMeasurable).mp hgsq |>.1] with x hfm hgm hfi hgi
  have hfx := (memLp_two_iff_integrable_sq_norm hfm).mpr hfi
  have hgx := (memLp_two_iff_integrable_sq_norm hgm).mpr hgi
  rw [integral_sub (hfx.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (hgx.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))]
  exact enorm_sub_integral_sq_le β hfx hgx

end PolycyclicRecognition

end

end OAI
