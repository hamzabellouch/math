import OAI.Analysis.LipschitzHilbert.Geometry.DyadicLineCover
import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineMaximal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Popular intervals produce maximal bad intervals in two fixed grids. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.DyadicLineGrid

def Bad (q : ℤ) (f : ℝ → ℝ) (β : ℝ) (k j : ℤ) : Prop :=
  β * scale k ≤ ∫ x in cell q k j, f x

theorem scale_le_iff {k l : ℤ} : scale k ≤ scale l ↔ k ≤ l :=
  zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)

theorem integrableOn_of_unit_bound {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {S : Set ℝ} (hS : volume S ≠ ∞) :
    IntegrableOn f S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound x).1] using (hbound x).2

/-- A popular interval fits in a bad dyadic interval, with only the factor-six
loss in the average and with the prescribed upper scale. -/
theorem popular_interval_has_bad {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {a b θ H : ℝ} {top : ℤ}
    (hab : a < b) (hθ : 0 ≤ θ) (hlen : b - a ≤ H) (htop : 6 * H ≤ scale top)
    (hpopular : θ * (b - a) ≤ ∫ x in Icc a b, f x) :
    ∃ q ∈ ({0, 1} : Finset ℤ), ∃ k j,
      k ≤ top ∧ Icc a b ⊆ cell q k j ∧ Bad q f (θ / 6) k j := by
  obtain ⟨q, hq, k, j, hcover, hsize⟩ := interval_cover hab
  have hk : k ≤ top := scale_le_iff.mp (hsize.trans ((mul_le_mul_of_nonneg_left hlen (by norm_num)).trans htop))
  have hint : IntegrableOn f (cell q k j) :=
    integrableOn_of_unit_bound hf hbound measure_Ico_lt_top.ne
  have hmono : (∫ x in Icc a b, f x) ≤ ∫ x in cell q k j, f x :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => (hbound x).1)
      (Filter.Eventually.of_forall fun _ hx => hcover hx)
  refine ⟨q, hq, k, j, hk, hcover, ?_⟩
  unfold Bad
  have hmul := mul_le_mul_of_nonneg_left hsize (div_nonneg hθ (by norm_num : (0 : ℝ) ≤ 6))
  nlinarith [hpopular.trans hmono]

/-- Hence every popular interval through a point is accounted for by a
maximal bad interval in one of the two fixed grids. -/
theorem popular_interval_has_maximalBad {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {a b θ H x : ℝ} {top : ℤ}
    (hab : a < b) (hθ : 0 ≤ θ) (hlen : b - a ≤ H) (htop : 6 * H ≤ scale top)
    (hx : x ∈ Icc a b) (hpopular : θ * (b - a) ≤ ∫ y in Icc a b, f y) :
    ∃ q ∈ ({0, 1} : Finset ℤ), ∃ k j,
      MaximalBad q top (Bad q f (θ / 6)) k j ∧ x ∈ cell q k j := by
  obtain ⟨q, hq, k, j, hk, hcover, hbad⟩ := popular_interval_has_bad hf hbound hab hθ hlen htop hpopular
  obtain ⟨l, i, hmax, hsub⟩ := exists_maximalBad hk hbad
  exact ⟨q, hq, l, i, hmax, hsub (hcover hx)⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
