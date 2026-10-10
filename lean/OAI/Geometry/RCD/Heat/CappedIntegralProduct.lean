import OAI.Geometry.RCD.Heat.HeatDensityL1Continuity

namespace OAI

/-! # Stability of capped overlap integrals in L¹ -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem integrable_min_nonneg {f : X → ℝ} (hf : Integrable f μ)
    (hf0 : ∀ x, 0 ≤ f x) (C : ℝ≥0) : Integrable (fun x => min (f x) C) μ := by
  apply hf.mono' ((continuous_id.min continuous_const).comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change |min (f x) C| ≤ f x
    rw [abs_of_nonneg (le_min (hf0 x) C.coe_nonneg)]
    exact min_le_left _ _

theorem integrable_capped_product {f g : X → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (C : ℝ≥0) :
    Integrable (fun x => min (f x) C * min (g x) C) μ :=
  (integrable_min_nonneg μ hf hf0 C).mul_bdd
    ((continuous_id.min continuous_const).comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg0 x) C.coe_nonneg)]
      exact min_le_right _ _)

private theorem capped_product_sub_le (C : ℝ≥0) {a b c d : ℝ}
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (_hd : 0 ≤ d) :
    |min a C * min b C - min c C * min d C| ≤ C * (|a - c| + |b - d|) := by
  have hac : |min a C - min c C| ≤ |a - c| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using!
      (LipschitzWith.id.min_const (C : ℝ)).dist_le_mul a c
  have hbd : |min b C - min d C| ≤ |b - d| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using!
      (LipschitzWith.id.min_const (C : ℝ)).dist_le_mul b d
  calc
    _ = |(min a C - min c C) * min b C + min c C * (min b C - min d C)| := by congr 1; ring
    _ ≤ |min a C - min c C| * |min b C| + |min c C| * |min b C - min d C| := by
      simpa only [abs_mul] using abs_add_le
        ((min a C - min c C) * min b C) (min c C * (min b C - min d C))
    _ ≤ |a - c| * C + C * |b - d| := by
      rw [abs_of_nonneg (le_min hb C.coe_nonneg), abs_of_nonneg (le_min hc C.coe_nonneg)]
      exact add_le_add (mul_le_mul hac (min_le_right _ _) (le_min hb C.coe_nonneg) (abs_nonneg _))
        (mul_le_mul (min_le_right _ _) hbd (abs_nonneg _) C.coe_nonneg)
    _ = _ := by ring

/-- Capping makes the overlap pairing continuous for the L¹ distance. -/
theorem integral_capped_product_sub_le {f g f' g' : X → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hf' : Integrable f' μ) (hg' : Integrable g' μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf0' : ∀ x, 0 ≤ f' x) (hg0' : ∀ x, 0 ≤ g' x) (C : ℝ≥0) :
    |(∫ x, min (f x) C * min (g x) C ∂μ) -
      (∫ x, min (f' x) C * min (g' x) C ∂μ)| ≤
      C * ((∫ x, |f x - f' x| ∂μ) + ∫ x, |g x - g' x| ∂μ) := by
  have hp := integrable_capped_product μ hf hg hf0 hg0 C
  have hq := integrable_capped_product μ hf' hg' hf0' hg0' C
  have hmajor : Integrable (fun x => (C : ℝ) * (|f x - f' x| + |g x - g' x|)) μ :=
    ((hf.sub hf').abs.add (hg.sub hg').abs).const_mul C
  rw [← integral_sub hp hq]
  calc
    _ ≤ ∫ x, |min (f x) C * min (g x) C - min (f' x) C * min (g' x) C| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => min (f x) C * min (g x) C - min (f' x) C * min (g' x) C)
    _ ≤ ∫ x, (C : ℝ) * (|f x - f' x| + |g x - g' x|) ∂μ :=
      integral_mono (hp.sub hq).abs hmajor (fun x => capped_product_sub_le C (hf0 x) (hg0 x) (hf0' x) (hg0' x))
    _ = _ := by
      rw [integral_const_mul]
      simpa only [Pi.sub_apply] using congrArg (fun a : ℝ => (C : ℝ) * a)
        (integral_add (hf.sub hf').abs (hg.sub hg').abs)

end RegularPointCoordinates

end

end OAI
