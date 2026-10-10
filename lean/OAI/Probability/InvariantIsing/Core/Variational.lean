import Mathlib

namespace OAI

/-!
# Spectral overlap deficit

The deficit `D` is equation (1.4) of the manuscript. Global bounded monotone
representatives are used for paths on `(0,1)`; endpoint values never enter the
integrals.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace InvariantIsing

/-- A bounded nondecreasing representative of an admissible overlap quantile. -/
structure OverlapPath where
  val : ℝ → ℝ
  monotone : Monotone val
  nonneg : ∀ s, 0 ≤ val s
  le_one : ∀ s, val s ≤ 1

instance : CoeFun OverlapPath (fun _ => ℝ → ℝ) := ⟨OverlapPath.val⟩

def pathMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

lemma pathMeasure_univ : pathMeasure Set.univ = 1 := by
  simp [pathMeasure]

instance : IsProbabilityMeasure pathMeasure := ⟨pathMeasure_univ⟩

lemma OverlapPath.measurable (p : OverlapPath) : Measurable p.val :=
  p.monotone.measurable

lemma OverlapPath.integrable (p : OverlapPath) : Integrable p.val pathMeasure := by
  apply (integrable_const (1 : ℝ)).mono' p.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (p.nonneg s)] using p.le_one s

lemma OverlapPath.integrable_posPart (p : OverlapPath) (r : ℝ) :
    Integrable (fun s => max (p s - r) 0) pathMeasure := by
  apply (integrable_const (max (1 - r) 0)).mono'
    ((p.measurable.sub measurable_const).max measurable_const).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le_max (sub_le_sub_right (p.le_one s) r) le_rfl

/-- Equation (1.4), defined also outside the interval for convenience. -/
def deficit (p : OverlapPath) (r : ℝ) : ℝ :=
  1 - r - ∫ s, max (p s - r) 0 ∂pathMeasure

@[simp] lemma deficit_one (p : OverlapPath) : deficit p 1 = 0 := by
  have he : (fun s => max (p s - 1) 0) = (fun _ => (0 : ℝ)) := by
    funext s
    exact max_eq_right (sub_nonpos.mpr (p.le_one s))
  simp [deficit, he]

lemma deficit_nonneg (p : OverlapPath) {r : ℝ} (hr : r ≤ 1) :
    0 ≤ deficit p r := by
  have h : (∫ s, max (p s - r) 0 ∂pathMeasure) ≤ 1 - r := by
    calc
      _ ≤ ∫ _, (1 - r) ∂pathMeasure := by
        apply integral_mono (p.integrable_posPart r) (integrable_const _)
        intro s
        exact max_le (sub_le_sub_right (p.le_one s) r) (sub_nonneg.mpr hr)
      _ = 1 - r := by simp
  unfold deficit
  linarith

lemma deficit_le (p : OverlapPath) (r : ℝ) : deficit p r ≤ 1 - r := by
  have h : 0 ≤ ∫ s, max (p s - r) 0 ∂pathMeasure :=
    integral_nonneg fun _ => le_max_right _ _
  unfold deficit
  linarith

lemma deficit_mem_unit (p : OverlapPath) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    deficit p r ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨deficit_nonneg p hr.2, (deficit_le p r).trans (by linarith [hr.1])⟩

@[simp] lemma deficit_zero (p : OverlapPath) :
    deficit p 0 = 1 - ∫ s, p s ∂pathMeasure := by
  have he : (fun s => max (p s) 0) = p.val := by
    funext s
    exact max_eq_left (p.nonneg s)
  simp only [deficit, sub_zero, he]

/-- Pointwise order of quantiles reverses the order of deficits. -/
lemma deficit_antitone_path (p q : OverlapPath) (hpq : ∀ s, p s ≤ q s) (r : ℝ) :
    deficit q r ≤ deficit p r := by
  have h : (∫ s, max (p s - r) 0 ∂pathMeasure) ≤
      ∫ s, max (q s - r) 0 ∂pathMeasure := by
    apply integral_mono (p.integrable_posPart r) (q.integrable_posPart r)
    intro s
    exact max_le_max (sub_le_sub_right (hpq s) r) le_rfl
  unfold deficit
  linarith

/-- A constant quantile has deficit `1 - max q r`. -/
def constantPath (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : OverlapPath where
  val := fun _ => q
  monotone := monotone_const
  nonneg := fun _ => hq.1
  le_one := fun _ => hq.2

lemma deficit_constant (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (r : ℝ) :
    deficit (constantPath q hq) r = 1 - max q r := by
  simp only [deficit, constantPath, integral_const, measureReal_def, pathMeasure_univ, ENNReal.toReal_one,
    one_smul]
  rcases le_total q r with h | h
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring

lemma complement_max_eq (a r : ℝ) :
    1 - max a r = 1 - r - max (a - r) 0 := by
  rcases le_total a r with h | h
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring

lemma OverlapPath.integrable_complement_max (p : OverlapPath) (r : ℝ) :
    Integrable (fun s => 1 - max (p s) r) pathMeasure := by
  simp_rw [complement_max_eq]
  exact (integrable_const (1 - r)).sub (p.integrable_posPart r)

lemma deficit_eq_integral (p : OverlapPath) (r : ℝ) :
    deficit p r = ∫ s, 1 - max (p s) r ∂pathMeasure := by
  simp_rw [complement_max_eq]
  rw [integral_sub (integrable_const _) (p.integrable_posPart r)]
  simp [deficit]

/-- The deficit is 1-Lipschitz in its scalar argument, including at atoms. -/
lemma abs_deficit_sub_le (p : OverlapPath) (r u : ℝ) :
    |deficit p r - deficit p u| ≤ |r - u| := by
  rw [deficit_eq_integral, deficit_eq_integral,
    ← integral_sub (p.integrable_complement_max r) (p.integrable_complement_max u)]
  have h := norm_integral_le_of_norm_le_const (μ := pathMeasure)
    (f := fun s => (1 - max (p s) r) - (1 - max (p s) u))
    (C := |r - u|) (Filter.Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs]
      have he : (1 - max (p s) r) - (1 - max (p s) u) =
          max u (p s) - max r (p s) := by rw [max_comm u, max_comm r]; ring
      rw [he]
      simpa only [abs_sub_comm] using abs_max_sub_max_le_abs u r (p s))
  simpa only [Real.norm_eq_abs, measureReal_def, pathMeasure_univ,
    ENNReal.toReal_one, mul_one] using h

lemma continuous_deficit (p : OverlapPath) : Continuous (deficit p) := by
  have hl : LipschitzWith 1 (deficit p) := by
    apply LipschitzWith.of_dist_le_mul
    intro r u
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_deficit_sub_le p r u
  exact hl.continuous

/-- Equation (4.10): uniform deficit error is bounded by the L¹ path error. -/
lemma abs_deficit_sub_path_le (p q : OverlapPath) (r : ℝ) :
    |deficit p r - deficit q r| ≤ ∫ s, |p s - q s| ∂pathMeasure := by
  rw [deficit_eq_integral, deficit_eq_integral,
    ← integral_sub (p.integrable_complement_max r) (q.integrable_complement_max r)]
  calc
    _ ≤ ∫ s, |(1 - max (p s) r) - (1 - max (q s) r)| ∂pathMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ s, |p s - q s| ∂pathMeasure := by
      apply integral_mono
        ((p.integrable_complement_max r).sub (q.integrable_complement_max r)).abs
        (p.integrable.sub q.integrable).abs
      intro s
      have he : (1 - max (p s) r) - (1 - max (q s) r) =
          -(max (p s) r - max (q s) r) := by ring
      change |(1 - max (p s) r) - (1 - max (q s) r)| ≤ |p s - q s|
      rw [he, abs_neg]
      exact abs_max_sub_max_le_abs (p s) (q s) r

end InvariantIsing

end

end OAI
