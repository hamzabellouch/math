import OAI.Analysis.LipschitzHilbert.Estimates.TopWeight
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-! Moving an actual popularity witness to a fixed reference line. -/

noncomputable section

open scoped NNReal

namespace LipschitzHilbert
namespace SlopeBox

/-- The point at horizontal coordinate `w.1` on the reference line through `z`. -/
def referencePoint (s : ℝ) (z w : ℝ × ℝ) : ℝ × ℝ :=
  (w.1, z.2 + s * (w.1 - z.1))

theorem horizontal_sub_identity (T : SlopeBox) (z w : ℝ × ℝ) :
    w.1 - z.1 = T.length * (T.horizontal w - T.horizontal z) := by
  unfold horizontal
  field_simp [T.length_pos.ne']
  ring

theorem transverse_sub_identity (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ) :
    w.2 - (referencePoint s z w).2 =
      T.width * (T.transverse w - T.transverse z) +
        (T.slope - s) * (w.1 - z.1) := by
  unfold transverse referencePoint
  dsimp
  field_simp [T.width_pos.ne']
  ring

/-- Box coordinates give the vertical distance to the reference line using
only the two actual points, with no choice of a point in a projection fiber. -/
theorem referencePoint_vertical_distance (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ) :
    |w.2 - (referencePoint s z w).2| ≤
      (T.radius w + T.radius z) * (T.width + T.length * |T.slope - s|) := by
  have hzw : |w.1 - z.1| ≤ T.length * (T.radius w + T.radius z) := by
    rw [T.horizontal_sub_identity, abs_mul, abs_of_pos T.length_pos]
    have htri := abs_sub (T.horizontal w) (T.horizontal z)
    have hw : |T.horizontal w| ≤ T.radius w := by
      unfold radius
      linarith [abs_nonneg (T.transverse w)]
    have hz : |T.horizontal z| ≤ T.radius z := by
      unfold radius
      linarith [abs_nonneg (T.transverse z)]
    exact mul_le_mul_of_nonneg_left (htri.trans (add_le_add hw hz)) T.length_pos.le
  have htrans : |T.transverse w - T.transverse z| ≤ T.radius w + T.radius z := by
    have hw : |T.transverse w| ≤ T.radius w := by
      unfold radius
      linarith [abs_nonneg (T.horizontal w)]
    have hz : |T.transverse z| ≤ T.radius z := by
      unfold radius
      linarith [abs_nonneg (T.horizontal z)]
    exact (abs_sub _ _).trans (add_le_add hw hz)
  rw [T.transverse_sub_identity]
  calc
    _ ≤ |T.width * (T.transverse w - T.transverse z)| +
        |(T.slope - s) * (w.1 - z.1)| := abs_add_le _ _
    _ = T.width * |T.transverse w - T.transverse z| +
        |T.slope - s| * |w.1 - z.1| := by
      rw [abs_mul, abs_mul, abs_of_pos T.width_pos]
    _ ≤ T.width * (T.radius w + T.radius z) +
        |T.slope - s| * (T.length * (T.radius w + T.radius z)) :=
      add_le_add (mul_le_mul_of_nonneg_left htrans T.width_pos.le)
        (mul_le_mul_of_nonneg_left hzw (abs_nonneg _))
    _ = _ := by ring

theorem referencePoint_vertical_distance_le (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ)
    {A K : ℝ} (hw : T.radius w ≤ A) (hz : T.radius z ≤ K) :
    |w.2 - (referencePoint s z w).2| ≤
      (A + K) * (T.width + T.length * |T.slope - s|) := by
  exact (T.referencePoint_vertical_distance s z w).trans
    (mul_le_mul_of_nonneg_right (add_le_add hw hz) (by
      have hl := T.length_pos
      have hw := T.width_pos
      positivity))

/-- The two points have the same horizontal coordinate, so a Lipschitz slope
field loses precisely their vertical distance. -/
theorem referencePoint_slope_error (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ)
    (u : ℝ × ℝ → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u) {δ A K : ℝ}
    (huw : |u w - T.slope| ≤ δ) (hw : T.radius w ≤ A) (hz : T.radius z ≤ K) :
    |u (referencePoint s z w) - T.slope| ≤
      δ + L * ((A + K) * (T.width + T.length * |T.slope - s|)) := by
  have hdist : dist (referencePoint s z w) w = |w.2 - (referencePoint s z w).2| := by
    simp [Prod.dist_eq, referencePoint, Real.dist_eq, abs_sub_comm]
  have hfield := hu.dist_le_mul (referencePoint s z w) w
  rw [Real.dist_eq, hdist] at hfield
  calc
    _ ≤ |u (referencePoint s z w) - u w| + |u w - T.slope| := abs_sub_le _ _ _
    _ ≤ L * |w.2 - (referencePoint s z w).2| + δ := add_le_add hfield huw
    _ ≤ L * ((A + K) * (T.width + T.length * |T.slope - s|)) + δ :=
      add_le_add (mul_le_mul_of_nonneg_left
        (T.referencePoint_vertical_distance_le s z w hw hz) L.coe_nonneg) le_rfl
    _ = _ := by ring

/-- The paper's small-time condition transfers a witness of precision `d`
to the reference line with angular error at most `(c+1)Δ/B²`. The width is
the actual enlarged width `m * length * d`, and `B² ≤ m`. -/
theorem transferred_slope_precision (T : SlopeBox) (s : ℝ) (z w : ℝ × ℝ)
    (u : ℝ × ℝ → ℝ) {L : ℝ≥0} (hu : LipschitzWith L u)
    {d m B c A K P : ℝ} (hd : 0 ≤ d) (hB : 0 < B) (hc : 0 ≤ c)
    (hw : T.radius w ≤ A) (hz : T.radius z ≤ K) (hP : A + K ≤ P)
    (hwidth : T.width = m * T.length * d) (hm : B ^ 2 ≤ m)
    (hprecision : d ≤ |T.slope - s| / B ^ 2)
    (hsmall : L * P * m * T.length ≤ 1 / 2)
    (huw : |u w - T.slope| ≤ c * d) :
    |u (referencePoint s z w) - T.slope| ≤ (c + 1) * |T.slope - s| / B ^ 2 := by
  have hAK : 0 ≤ A + K := by
    linarith [T.radius_nonnegative w, T.radius_nonnegative z]
  have hP0 : 0 ≤ P := hAK.trans hP
  have hlength := T.length_pos
  have hwidth0 := T.width_pos
  let a : ℝ := L * P * T.length
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have ham : a * m ≤ 1 / 2 := by dsimp [a]; nlinarith [hsmall]
  have haB : a * B ^ 2 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hm ha).trans ham
  have habound : a ≤ (1 / 2) / B ^ 2 := (le_div_iff₀ (sq_pos_of_pos hB)).2 haB
  have hwidthError : a * m * d ≤ (1 / 2) * (|T.slope - s| / B ^ 2) :=
    (mul_le_mul_of_nonneg_right ham hd).trans
      (mul_le_mul_of_nonneg_left hprecision (by norm_num))
  have hlengthError : a * |T.slope - s| ≤ (1 / 2) * (|T.slope - s| / B ^ 2) := by
    have hh := mul_le_mul_of_nonneg_right habound (abs_nonneg (T.slope - s))
    calc
      _ ≤ (1 / 2) / B ^ 2 * |T.slope - s| := hh
      _ = _ := by ring
  have hmotion : L * ((A + K) * (T.width + T.length * |T.slope - s|)) ≤
      |T.slope - s| / B ^ 2 := by
    calc
      _ ≤ L * (P * (T.width + T.length * |T.slope - s|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hP (by positivity)) L.coe_nonneg
      _ = a * m * d + a * |T.slope - s| := by rw [hwidth]; dsimp [a]; ring
      _ ≤ _ := by linarith
  have hwitness := mul_le_mul_of_nonneg_left hprecision hc
  have herr := T.referencePoint_slope_error s z w u hu huw hw hz
  calc
    _ ≤ c * d + L * ((A + K) * (T.width + T.length * |T.slope - s|)) := herr
    _ ≤ c * (|T.slope - s| / B ^ 2) + |T.slope - s| / B ^ 2 :=
      add_le_add hwitness hmotion
    _ = _ := by ring

end SlopeBox
end LipschitzHilbert

end

end OAI
