import OAI.Probability.SLE.Gauge.RibbonStepPatch

namespace OAI

/-! Fixed bi-Lipschitz constants for the normal ribbon of a unit-speed
curve whose tangent changes at rate at most 1/50. This is the local
analytic estimate for the explicit serpentine's straight and circular pieces. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine

def normalRibbon (σ tangent : ℝ → ℂ) (z : ℂ) : ℂ :=
  σ z.re + (z.im : ℂ) * Complex.I * tangent z.re

lemma curve_linear_error
    (σ tangent : ℝ → ℂ) (a b : ℝ) (hab : b - a ≤ 4)
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt σ (tangent t) (Icc a b) t)
    (hL : LipschitzOnWith (1 / 50) tangent (Icc a b))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖σ s - σ t - ((s - t : ℝ) : ℂ) * tangent t‖ ≤ (4 / 50 : ℝ) * |s - t| := by
  let f := fun u : ℝ => σ u - (u : ℂ) * tangent t
  have hf (u : ℝ) (hu : u ∈ Icc a b) :
      HasDerivWithinAt f (tangent u - tangent t) (Icc a b) u := by
    convert (hd u hu).sub
      ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const (tangent t)).hasDerivWithinAt using 1 <;>
      simp only [f, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    rfl
  have hbound (u : ℝ) (hu : u ∈ Icc a b) : ‖tangent u - tangent t‖ ≤ (4 / 50 : ℝ) := by
    have hdut : dist u t ≤ 4 := by
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith [hu.1, hu.2, ht.1, ht.2]
    have hh := hL.dist_le_mul u hu t ht
    rw [dist_eq_norm] at hh
    exact hh.trans (by norm_num; linarith)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound
    (convex_Icc a b) ht hs
  have he : f s - f t = σ s - σ t - ((s - t : ℝ) : ℂ) * tangent t := by
    dsimp only [f]
    push_cast
    ring
  rw [he, Real.norm_eq_abs] at hh
  exact hh

/-- A length-four patch has fixed constants 2 in both directions. -/
theorem normalRibbon_patch_bounds
    (σ tangent : ℝ → ℂ) (a b : ℝ) (hab : b - a ≤ 4)
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt σ (tangent t) (Icc a b) t)
    (hunit : ∀ t ∈ Icc a b, ‖tangent t‖ = 1)
    (hL : LipschitzOnWith (1 / 50) tangent (Icc a b))
    (z w : ℂ) (hz : z.re ∈ Icc a b ∧ |z.im| ≤ 1)
    (hw : w.re ∈ Icc a b ∧ |w.im| ≤ 1) :
    dist (normalRibbon σ tangent z) (normalRibbon σ tangent w) ≤ 2 * dist z w ∧
      dist z w ≤ 2 * dist (normalRibbon σ tangent z) (normalRibbon σ tangent w) := by
  let E := σ z.re - σ w.re - ((z.re - w.re : ℝ) : ℂ) * tangent w.re
  have hE : ‖E‖ ≤ (4 / 50 : ℝ) * |z.re - w.re| :=
    curve_linear_error σ tangent a b hab hd hL hz.1 hw.1
  have hT := hL.dist_le_mul z.re hz.1 w.re hw.1
  rw [dist_eq_norm, Real.dist_eq] at hT
  have hnorm : ‖(z.im : ℂ) * Complex.I * (tangent z.re - tangent w.re)‖ ≤
      (1 / 50 : ℝ) * |z.re - w.re| := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    calc
      _ ≤ 1 * ‖tangent z.re - tangent w.re‖ := mul_le_mul_of_nonneg_right hz.2 (norm_nonneg _)
      _ ≤ _ := by simpa using hT
  let D := normalRibbon σ tangent z - normalRibbon σ tangent w
  let A := (z - w) * tangent w.re
  have he : D - A = E + (z.im : ℂ) * Complex.I * (tangent z.re - tangent w.re) := by
    have hzw : z - w = ((z.re - w.re : ℝ) : ℂ) +
        ((z.im - w.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    dsimp only [D, A, E, normalRibbon]
    rw [hzw]
    push_cast
    ring
  have her : ‖D - A‖ ≤ (1 / 10 : ℝ) * ‖z - w‖ := by
    rw [he]
    have hh := (norm_add_le E _).trans (add_le_add hE hnorm)
    have hre : |z.re - w.re| ≤ ‖z - w‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - w)
    nlinarith
  have hA : ‖A‖ = ‖z - w‖ := by
    change ‖(z - w) * tangent w.re‖ = _
    rw [norm_mul, hunit _ hw.1, mul_one]
  have hupper : ‖D‖ ≤ ‖z - w‖ + ‖D - A‖ := by
    have hh := norm_add_le A (D - A)
    rw [add_sub_cancel, hA] at hh
    exact hh
  have hlower : ‖z - w‖ ≤ ‖D‖ + ‖D - A‖ := by
    have hh := norm_sub_le D (D - A)
    rw [sub_sub_cancel, hA] at hh
    exact hh
  simp only [dist_eq_norm]
  change ‖D‖ ≤ 2 * ‖z - w‖ ∧ ‖z - w‖ ≤ 2 * ‖D‖
  constructor <;> nlinarith [norm_nonneg D, norm_nonneg (z - w)]

end SLEExactGauge.Serpentine

end

end OAI
