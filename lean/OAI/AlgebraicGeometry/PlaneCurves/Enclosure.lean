import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OAI

/-!
# Enclosing polygons and real slice profiles
-/

section

/-!
Real-coordinate enclosure in §04, Lemma `exponent-enclosure` of the manuscript
at fd47dd0a0011f54e9e1ca9c45cb9d022f25c2d30. These are finite geometry lemmas;
no assertion identifying a geometric section space with an exponent set is made.
-/
namespace Nagata.ExponentEnclosure

noncomputable def positivePart (x : ℝ) : ℝ := max x 0

def exponentPolygon (ρ a Δ X Y : ℝ) : Prop :=
  0 ≤ X ∧ X ≤ 1 + ρ / 9 ∧
    -a * X + Δ * positivePart (X - 1) ≤ Y ∧
    Y ≤ -a * X + ρ + (Δ - 9) * positivePart (X - 1)

def enclosingPolygon (a lam X Y : ℝ) : Prop :=
  0 ≤ X ∧ -a * X ≤ Y ∧
    Y ≤ -a * X + lam * a - 9 * positivePart (X - lam)

lemma positivePart_of_nonpos {x : ℝ} (h : x ≤ 0) : positivePart x = 0 :=
  max_eq_right h

lemma positivePart_of_nonneg {x : ℝ} (h : 0 ≤ x) : positivePart x = x :=
  max_eq_left h

/-- The source polygon is contained in D_lam, including its upper-index tip.
The hypotheses here are weaker than the manuscript's positive parameter bounds. -/
theorem polygon_containment {ρ a Δ lam X Y : ℝ}
    (hρ : 0 ≤ ρ) (hΔ : 0 ≤ Δ) (hlam : lam ≤ 1)
    (hslack : ρ + Δ * ρ / 9 < lam * a - 9 * (1 - lam))
    (h : exponentPolygon ρ a Δ X Y) : enclosingPolygon a lam X Y := by
  rcases h with ⟨hX, hXtop, hYlo, hYhi⟩
  refine ⟨hX, ?_, ?_⟩
  · have hp : 0 ≤ positivePart (X - 1) := le_max_right _ _
    have hprod := mul_nonneg hΔ hp
    linarith
  · by_cases hXone : X ≤ 1
    · rw [positivePart_of_nonpos (by linarith : X - 1 ≤ 0)] at hYhi
      have hmax : positivePart (X - lam) ≤ 1 - lam := by
        exact max_le (by linarith) (by linarith)
      have hprod := mul_nonneg hΔ hρ
      nlinarith
    · have hXone' : 1 ≤ X := le_of_lt (lt_of_not_ge hXone)
      rw [positivePart_of_nonneg (by linarith : 0 ≤ X - 1)] at hYhi
      rw [positivePart_of_nonneg (by linarith : 0 ≤ X - lam)]
      have hscaled : Δ * (X - 1) ≤ Δ * (ρ / 9) :=
        mul_le_mul_of_nonneg_left (by linarith) hΔ
      nlinarith

/-- The degree-zero block lies exactly on both boundary lines. -/
theorem degree_zero_tip {ρ a Δ : ℝ} (hρ : 0 ≤ ρ) :
    exponentPolygon ρ a Δ (1 + ρ / 9) (-a - ρ / 9 * (a - Δ)) := by
  unfold exponentPolygon
  rw [positivePart_of_nonneg (by linarith : 0 ≤ 1 + ρ / 9 - 1)]
  constructor
  · linarith
  constructor
  · exact le_rfl
  constructor <;> nlinarith

/-- Normalization of a first-branch exponent interval, j ≤ m. -/
theorem first_interval_normalized {ρ a Δ m j K U : ℝ}
    (hm : 0 < m) (hρ : 0 ≤ ρ) (hj : 0 ≤ j) (hjm : j ≤ m)
    (hlo : U - a * j < K) (hhi : K < U - a * j + m * ρ) :
    exponentPolygon ρ a Δ (j / m) ((K - U) / m) := by
  have hdiv : j / m ≤ 1 := (div_le_one hm).mpr hjm
  unfold exponentPolygon
  rw [positivePart_of_nonpos (by linarith : j / m - 1 ≤ 0)]
  refine ⟨div_nonneg hj hm.le, by linarith, ?_, ?_⟩
  · simp only [mul_zero, add_zero]
    apply (le_div_iff₀ hm).mpr
    have heq : -a * (j / m) * m = -a * j := by field_simp [ne_of_gt hm]
    rw [heq]
    linarith
  · simp only [mul_zero, add_zero]
    apply (div_le_iff₀ hm).mpr
    have heq : (-a * (j / m) + ρ) * m = -a * j + m * ρ := by
      field_simp [ne_of_gt hm]
    rw [heq]
    linarith

/-- Normalization of a second-branch interval expressed relative to U_0. -/
theorem second_interval_normalized {ρ a Δ m j K U : ℝ}
    (hm : 0 < m) (hjm : m ≤ j) (hjtop : j ≤ m * (1 + ρ / 9))
    (hlo : U - a * j + Δ * (j - m) ≤ K)
    (hhi : K ≤ U - a * j + m * ρ + (Δ - 9) * (j - m)) :
    exponentPolygon ρ a Δ (j / m) ((K - U) / m) := by
  have hdiv : 1 ≤ j / m := (one_le_div hm).mpr hjm
  unfold exponentPolygon
  rw [positivePart_of_nonneg (by linarith : 0 ≤ j / m - 1)]
  refine ⟨by linarith, (div_le_iff₀ hm).mpr (by nlinarith), ?_, ?_⟩
  · apply (le_div_iff₀ hm).mpr
    have heq : (-a * (j / m) + Δ * (j / m - 1)) * m =
        -a * j + Δ * (j - m) := by field_simp [ne_of_gt hm]
    rw [heq]
    linarith
  · apply (div_le_iff₀ hm).mpr
    have heq : (-a * (j / m) + ρ + (Δ - 9) * (j / m - 1)) * m =
        -a * j + m * ρ + (Δ - 9) * (j - m) := by field_simp [ne_of_gt hm]
    rw [heq]
    linarith

/-- Algebraic identity identifying the lower interval endpoint in the second branch. -/
theorem second_lower_endpoint (a Δ m j h : ℝ) :
    (h - 9 * (j - m)) / 9 * (a - Δ) - (h / 9 * (a - Δ) + m * a) =
      -a * j + Δ * (j - m) := by ring

/-- The corresponding upper endpoint after adding the interval length n. -/
theorem second_upper_endpoint (a Δ m j h : ℝ) :
    (h - 9 * (j - m)) / 9 * (a - Δ) + (h - 9 * (j - m)) -
        (h / 9 * (a - Δ) + m * a) =
      -a * j + h + (Δ - 9) * (j - m) := by ring

/-- Raw exponent conditions of (exponent-set), using real indices so the numerical
argument does not depend on integrality. `d / 3` replaces its integer floor;
for integral j the bounds are equivalent. -/
def rawExponent (d m h a Δ j K : ℝ) : Prop :=
  (0 ≤ j ∧ j ≤ m ∧
    h / 9 * (a - Δ) + (m - j) * a < K ∧
    K < h / 9 * (a - Δ) + (m - j) * a + h) ∨
  (m < j ∧ j ≤ d / 3 ∧ 0 < d - 3 * j ∧
    (h - 9 * (j - m)) / 9 * (a - Δ) < K ∧
    K < (h - 9 * (j - m)) / 9 * (a - Δ) + (h - 9 * (j - m))) ∨
  (m < j ∧ j ≤ d / 3 ∧ d - 3 * j = 0 ∧ K = 0)

/-- Every raw exponent obeys the manuscript's polygon inequalities. -/
theorem rawExponent_normalized {d m h ρ a Δ j K : ℝ}
    (hm : 0 < m) (hρ : 0 ≤ ρ) (hdegree : h = 3 * (d - 3 * m))
    (hratio : h = m * ρ) (hmem : rawExponent d m h a Δ j K) :
    exponentPolygon ρ a Δ (j / m)
      ((K - (h / 9 * (a - Δ) + m * a)) / m) := by
  rcases hmem with hfirst | hsecond | htip
  · rcases hfirst with ⟨hj, hjm, hlo, hhi⟩
    apply first_interval_normalized hm hρ hj hjm
    · nlinarith [hlo]
    · nlinarith [hhi]
  · rcases hsecond with ⟨hjm, hjtop, _, hlo, hhi⟩
    apply second_interval_normalized hm hjm.le
    · nlinarith
    · have hid := second_lower_endpoint a Δ m j h
      linarith
    · have hid := second_upper_endpoint a Δ m j h
      nlinarith
  · rcases htip with ⟨_, _, hzero, hK⟩
    have hj : j / m = 1 + ρ / 9 := by
      apply (div_eq_iff (ne_of_gt hm)).mpr
      nlinarith
    have hY : (K - (h / 9 * (a - Δ) + m * a)) / m =
        -a - ρ / 9 * (a - Δ) := by
      apply (div_eq_iff (ne_of_gt hm)).mpr
      rw [hK, hratio]
      ring
    rw [hj, hY]
    exact degree_zero_tip hρ

/-- The integer exponent-set arithmetic maps into the enclosing polygon. This
uses actual integer indices, without assuming any analytic/geometric bridge. -/
theorem integer_exponent_enclosure {d m h ρ a Δ lam : ℝ} {j K : ℤ}
    (hm : 0 < m) (hρ : 0 ≤ ρ) (hΔ : 0 ≤ Δ) (hlam : lam ≤ 1)
    (hdegree : h = 3 * (d - 3 * m)) (hratio : h = m * ρ)
    (hslack : ρ + Δ * ρ / 9 < lam * a - 9 * (1 - lam))
    (hmem : rawExponent d m h a Δ (j : ℝ) (K : ℝ)) :
    enclosingPolygon a lam ((j : ℝ) / m)
      (((K : ℝ) - (h / 9 * (a - Δ) + m * a)) / m) :=
  polygon_containment hρ hΔ hlam hslack
    (rawExponent_normalized hm hρ hdegree hratio hmem)

end Nagata.ExponentEnclosure

end

section

noncomputable section

namespace Nagata.W04

/-- Membership in the enclosing polygon D_lambda, with a left explicit. -/
def InPolygon (a lam x y : ℝ) : Prop :=
  0 ≤ x ∧ -a * x ≤ y ∧ y ≤ -a * x + lam * a - 9 * max (x - lam) 0

/-- Dilation by any positive real factor preserves the actual inequalities. -/
theorem polygon_dilation (a lam scale x y : ℝ) (hscale : 0 < scale) :
    InPolygon a (scale * lam) (scale * x) (scale * y) ↔ InPolygon a lam x y := by
  have hmax : max (scale * x - scale * lam) 0 = scale * max (x - lam) 0 := by
    rw [mul_max_of_nonneg _ _ (le_of_lt hscale)]
    congr 1 <;> ring
  unfold InPolygon
  rw [hmax]
  have hlo : -a * (scale * x) = scale * (-a * x) := by ring
  have hup : -a * (scale * x) + (scale * lam) * a - 9 * (scale * max (x - lam) 0) =
      scale * (-a * x + lam * a - 9 * max (x - lam) 0) := by ring
  rw [hup, hlo]
  simp only [mul_nonneg_iff_of_pos_left hscale, mul_le_mul_iff_right₀ hscale]

/-- Positive coordinate dilation gives exactly D_lambda = lambda D_1. -/
theorem polygon_scaling (a lam x y : ℝ) (hlam : 0 < lam) :
    InPolygon a lam (lam * x) (lam * y) ↔ InPolygon a 1 x y := by
  simpa using polygon_dilation a 1 lam x y hlam

private theorem le_one_sub_div_iff (a x y : ℝ) (ha : 0 < a) :
    x ≤ 1 - y / a ↔ a * x ≤ a - y := by
  have h : x ≤ 1 - y / a ↔ y / a ≤ 1 - x := by constructor <;> intro h <;> linarith
  rw [h, div_le_iff₀ ha]
  constructor <;> intro h <;> nlinarith

/-- Exact horizontal slice above the horizontal axis; empty cases are included. -/
theorem positive_slice (a x y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    InPolygon a 1 x y ↔ 0 ≤ x ∧ x ≤ 1 - y / a := by
  rw [le_one_sub_div_iff a x y ha]
  constructor
  · rintro ⟨hx, hlo, hup⟩
    refine ⟨hx, ?_⟩
    have hm := le_max_right (x - 1) (0 : ℝ)
    nlinarith
  · rintro ⟨hx, hup⟩
    have hx1 : x ≤ 1 := by nlinarith
    unfold InPolygon
    rw [max_eq_right (by linarith : x - 1 ≤ 0)]
    refine ⟨hx, ?_, ?_⟩
    · have hax : 0 ≤ a * x := mul_nonneg (le_of_lt ha) hx
      nlinarith
    · nlinarith

/-- Exact horizontal slice below the horizontal axis; empty cases are included. -/
theorem negative_slice (a x y : ℝ) (ha : 0 < a) (hy : y ≤ 0) :
    InPolygon a 1 x y ↔ -y / a ≤ x ∧ x ≤ 1 - y / (a + 9) := by
  have ha9 : 0 < a + 9 := by linarith
  rw [div_le_iff₀ ha, le_one_sub_div_iff (a + 9) x y ha9]
  constructor
  · rintro ⟨hx, hlo, hup⟩
    refine ⟨by nlinarith, ?_⟩
    have hm := le_max_left (x - 1) (0 : ℝ)
    nlinarith
  · rintro ⟨hlo, hup⟩
    have hx : 0 ≤ x := by nlinarith
    refine ⟨hx, by nlinarith, ?_⟩
    by_cases hx1 : x ≤ 1
    · rw [max_eq_right (by linarith : x - 1 ≤ 0)]
      have hax : a * x ≤ a := by nlinarith
      nlinarith
    · rw [max_eq_left (by linarith : 0 ≤ x - 1)]
      nlinarith

/-- The negative-height interval width in the manuscript has the asserted slope. -/
theorem negative_width_identity (a y : ℝ) (ha : 0 < a) :
    (1 - y / (a + 9)) - (-y / a) = 1 + y / (a * (1 + a / 9)) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have ha90 : a + 9 ≠ 0 := ne_of_gt (by linarith)
  have ht : 1 + a / 9 ≠ 0 := ne_of_gt (by
    have h := div_pos ha (show (0 : ℝ) < 9 by norm_num)
    linarith)
  field_simp
  ring

/-- Canonical width formula; negative values signify an empty slice. -/
def UnitSliceWidth (a y : ℝ) : ℝ :=
  if 0 ≤ y then 1 - y / a else 1 + y / (a * (1 + a / 9))

/-- Left endpoint of the affine horizontal slice. -/
def SliceLower (a y : ℝ) : ℝ := if 0 ≤ y then 0 else -y / a

/-- Right endpoint of the affine horizontal slice. -/
def SliceUpper (a y : ℝ) : ℝ :=
  if 0 ≤ y then 1 - y / a else 1 - y / (a + 9)

/-- The width formula is the actual difference of interval endpoints. -/
theorem unit_slice_width (a y : ℝ) (ha : 0 < a) :
    SliceUpper a y - SliceLower a y = UnitSliceWidth a y := by
  by_cases hy : 0 ≤ y
  · simp [SliceUpper, SliceLower, UnitSliceWidth, hy]
  · simp only [SliceUpper, SliceLower, UnitSliceWidth, ite_eq_right hy]
    exact negative_width_identity a y ha

/-- The endpoint functions describe the polygon's actual slice exactly. -/
theorem unit_slice_interval (a x y : ℝ) (ha : 0 < a) :
    InPolygon a 1 x y ↔ SliceLower a y ≤ x ∧ x ≤ SliceUpper a y := by
  by_cases hy : 0 ≤ y
  · simp only [SliceLower, SliceUpper, ite_eq_left hy]
    exact positive_slice a x y ha hy
  · simp only [SliceLower, SliceUpper, ite_eq_right hy]
    exact negative_slice a x y ha (le_of_lt (lt_of_not_ge hy))

/-- Nonnegative width is exactly nonemptiness; both endpoint tips are retained. -/
theorem unit_slice_nonempty (a y : ℝ) (ha : 0 < a) :
    (∃ x, InPolygon a 1 x y) ↔ 0 ≤ UnitSliceWidth a y := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨hl, hu⟩ := (unit_slice_interval a x y ha).mp hx
    rw [← unit_slice_width a y ha]
    linarith
  · intro h
    refine ⟨SliceLower a y, (unit_slice_interval a _ y ha).mpr ⟨le_rfl, ?_⟩⟩
    rw [← unit_slice_width a y ha] at h
    linarith

/-- No horizontal slice has width greater than one. -/
theorem unit_width_le_one (a y : ℝ) (ha : 0 < a) : UnitSliceWidth a y ≤ 1 := by
  unfold UnitSliceWidth
  split_ifs with hy
  · have h := div_nonneg hy (le_of_lt ha)
    linarith
  · have hA : 0 ≤ a * (1 + a / 9) := mul_nonneg (le_of_lt ha) (by
      have h := div_pos ha (show (0 : ℝ) < 9 by norm_num)
      linarith)
    have h := div_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hy)) hA
    linarith

/-- The width threshold yields a single closed interval of heights. -/
theorem unit_width_threshold (a y s : ℝ) (ha : 0 < a)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s ≤ UnitSliceWidth a y ↔
      -a * (1 + a / 9) * (1 - s) ≤ y ∧ y ≤ a * (1 - s) := by
  have hA : 0 < a * (1 + a / 9) := mul_pos ha (by
    have h := div_pos ha (show (0 : ℝ) < 9 by norm_num)
    linarith)
  have htop : 0 ≤ a * (1 - s) := by
    have hsabs : |s| ≤ 1 := (abs_of_nonneg hs).symm ▸ hs1
    exact mul_nonneg ha.le (sub_nonneg.mpr (le_abs_self s |>.trans hsabs))
  have hbot : -a * (1 + a / 9) * (1 - s) ≤ 0 := by
    nlinarith [mul_nonneg (le_of_lt hA) (show 0 ≤ 1 - s by linarith)]
  unfold UnitSliceWidth
  split_ifs with hy
  · rw [le_one_sub_div_iff a s y ha]
    constructor <;> intro h
    · exact ⟨le_trans hbot hy, by nlinarith⟩
    · nlinarith [h.2]
  · have hy0 : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
    have hid : 1 + y / (a * (1 + a / 9)) =
        1 - (-y) / (a * (1 + a / 9)) := by ring
    rw [hid, le_one_sub_div_iff (a * (1 + a / 9)) s (-y) hA]
    constructor <;> intro h
    · exact ⟨by nlinarith, le_trans hy0 htop⟩
    · nlinarith [h.1]

/-- Width after positive dilation and arbitrary vertical translation. -/
def ScaledSliceWidth (a scale U y : ℝ) : ℝ :=
  scale * UnitSliceWidth a ((y - U) / scale)

/-- Every scaled horizontal slice has width at most the dilation factor. -/
theorem scaled_width_le_scale (a scale U y : ℝ) (ha : 0 < a) (hscale : 0 ≤ scale) :
    ScaledSliceWidth a scale U y ≤ scale := by
  unfold ScaledSliceWidth
  simpa using mul_le_mul_of_nonneg_left (unit_width_le_one a ((y - U) / scale) ha) hscale

/-- Positive scaling and translation preserve the exact endpoint description. -/
theorem scaled_slice_interval (a scale U x y : ℝ) (ha : 0 < a) (hscale : 0 < scale) :
    InPolygon a scale x (y - U) ↔
      scale * SliceLower a ((y - U) / scale) ≤ x ∧
      x ≤ scale * SliceUpper a ((y - U) / scale) := by
  have hp := polygon_scaling a scale (x / scale) ((y - U) / scale) hscale
  rw [mul_div_cancel₀ _ (ne_of_gt hscale), mul_div_cancel₀ _ (ne_of_gt hscale)] at hp
  rw [hp, unit_slice_interval a (x / scale) ((y - U) / scale) ha]
  rw [le_div_iff₀ hscale, div_le_iff₀ hscale]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

/-- The scaled width also equals the difference of its actual endpoints. -/
theorem scaled_slice_width (a scale U y : ℝ) (ha : 0 < a) :
    scale * SliceUpper a ((y - U) / scale) -
      scale * SliceLower a ((y - U) / scale) = ScaledSliceWidth a scale U y := by
  rw [← mul_sub, unit_slice_width a ((y - U) / scale) ha]
  rfl

/-- The exact closed height interval, including both zero-width tips. -/
theorem scaled_width_threshold (a scale U y s : ℝ)
    (ha : 0 < a) (hscale : 0 < scale) (hs : 0 ≤ s) (hsupper : s ≤ scale) :
    s ≤ ScaledSliceWidth a scale U y ↔
      U - a * (1 + a / 9) * (scale - s) ≤ y ∧
      y ≤ U + a * (scale - s) := by
  have hsunit : s / scale ≤ 1 := by
    rw [div_le_iff₀ hscale]
    simpa using hsupper
  unfold ScaledSliceWidth
  have hw : s ≤ scale * UnitSliceWidth a ((y - U) / scale) ↔
      s / scale ≤ UnitSliceWidth a ((y - U) / scale) := by
    rw [div_le_iff₀ hscale]
    rw [mul_comm]
  rw [hw, unit_width_threshold a ((y - U) / scale) (s / scale) ha
    (div_nonneg hs (le_of_lt hscale)) hsunit]
  rw [le_div_iff₀ hscale, div_le_iff₀ hscale]
  have hid (c : ℝ) : c * (1 - s / scale) * scale = c * (scale - s) := by
    field_simp
  rw [hid, hid]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

/-- Length of the interval of heights in the threshold theorem. -/
theorem height_interval_length (a scale U s : ℝ) :
    (U + a * (scale - s)) - (U - a * (1 + a / 9) * (scale - s)) =
      (2 * a + a ^ 2 / 9) * (scale - s) := by ring

end Nagata.W04

end
end

end OAI
