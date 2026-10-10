import OAI.Analysis.SphereIsometry.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-!
# Contact of a ray from an interior point with the unit sphere

The contact radius exists by the intermediate value theorem on a real interval.
A quantitative comparison proves both uniqueness and Lipschitz continuity. No
compactness of the ambient unit ball or support functional is used.
-/

noncomputable section

namespace Tingley

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Comparison of two contacts, with the radii in increasing order. The vectors
need not be unit vectors for this estimate. -/
theorem contact_comparison_ordered (c v w : X) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s)
    (hvr : ‖c + r • v‖ = 1) (hws : ‖c + s • w‖ = 1) :
    (1 - ‖c‖) * (s - r) ≤ (r * s) * ‖v - w‖ := by
  have hs : 0 ≤ s := hr.trans hrs
  have hsr : 0 ≤ s - r := sub_nonneg.mpr hrs
  have hprod : 0 ≤ r * s := mul_nonneg hr hs
  have he : s • (c + r • v) =
      (s - r) • c + r • (c + s • w) + (r * s) • (v - w) := by
    simp only [smul_add, sub_smul, smul_sub, smul_smul, mul_comm s r]
    abel
  have hbound : s ≤ (s - r) * ‖c‖ + r + (r * s) * ‖v - w‖ := by
    calc
      s = ‖s • (c + r • v)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hs, hvr, mul_one]
      _ = ‖(s - r) • c + r • (c + s • w) + (r * s) • (v - w)‖ :=
        congrArg norm he
      _ ≤ ‖(s - r) • c + r • (c + s • w)‖ + ‖(r * s) • (v - w)‖ :=
        norm_add_le _ _
      _ ≤ (‖(s - r) • c‖ + ‖r • (c + s • w)‖) + ‖(r * s) • (v - w)‖ :=
        add_le_add_left (norm_add_le _ _) _
      _ = (s - r) * ‖c‖ + r + (r * s) * ‖v - w‖ := by
        simp only [norm_smul, Real.norm_of_nonneg hsr, Real.norm_of_nonneg hr,
          Real.norm_of_nonneg hprod, hws, mul_one]
  nlinarith [hbound]

/-- A symmetric contact comparison, still independent of unit-norm assumptions
on the two direction vectors. -/
theorem contact_comparison (c v w : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hvr : ‖c + r • v‖ = 1) (hws : ‖c + s • w‖ = 1) :
    (1 - ‖c‖) * |r - s| ≤ (r * s) * ‖v - w‖ := by
  rcases le_total r s with hrs | hsr
  · calc
      (1 - ‖c‖) * |r - s| = (1 - ‖c‖) * (s - r) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hrs)]
        ring
      _ ≤ (r * s) * ‖v - w‖ := contact_comparison_ordered c v w hr hrs hvr hws
  · rw [abs_of_nonneg (sub_nonneg.mpr hsr)]
    simpa only [mul_comm s r, norm_sub_rev w v] using
      contact_comparison_ordered c w v hs hsr hws hvr

/-- Nonnegative contacts in the same direction are unique when the center is
strictly inside the unit ball. -/
theorem contact_unique (c : X) (hc : ‖c‖ < 1) (v : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hvr : ‖c + r • v‖ = 1) (hvs : ‖c + s • v‖ = 1) : r = s := by
  have h := contact_comparison c v v hr hs hvr hvs
  rw [sub_self, norm_zero, mul_zero] at h
  have hL : 0 < 1 - ‖c‖ := sub_pos.mpr hc
  have hz : |r - s| ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact (not_lt_of_ge h) (mul_pos hL hpos)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

/-- Every nonnegative contact in a unit direction has the exact radial
bounds, independently of how the contact was obtained. -/
theorem contact_bounds (c : X) (v : UnitSphere X) {r : ℝ}
    (hr : 0 ≤ r) (hcontact : ‖c + r • (v : X)‖ = 1) :
    1 - ‖c‖ ≤ r ∧ r ≤ 1 + ‖c‖ := by
  have hn : ‖r • (v : X)‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr, v.property, mul_one]
  have hlo := norm_add_le c (r • (v : X))
  rw [hcontact, hn] at hlo
  have hhi := norm_sub_le (c + r • (v : X)) c
  have he : (c + r • (v : X)) - c = r • (v : X) := by abel
  rw [he, hn, hcontact] at hhi
  constructor <;> linarith

/-- The genuine positive contact on each ray from an interior center. Existence
uses only a compact real interval, never compactness of the ambient sphere. -/
theorem existsUnique_radialContact (c : X) (hc : ‖c‖ < 1)
    (v : UnitSphere X) : ∃! r : ℝ, 0 < r ∧ ‖c + r • (v : X)‖ = 1 := by
  have hL : 0 < 1 - ‖c‖ := sub_pos.mpr hc
  have hU : 0 ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
  have hLU : 1 - ‖c‖ ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
  have hleft : ‖c + (1 - ‖c‖) • (v : X)‖ ≤ 1 := by
    calc
      ‖c + (1 - ‖c‖) • (v : X)‖ ≤ ‖c‖ + ‖(1 - ‖c‖) • (v : X)‖ :=
        norm_add_le _ _
      _ = 1 := by
        rw [norm_smul, Real.norm_of_nonneg hL.le, v.property, mul_one]
        ring
  have hright : 1 ≤ ‖c + (1 + ‖c‖) • (v : X)‖ := by
    have h := norm_sub_le (c + (1 + ‖c‖) • (v : X)) c
    have he : (c + (1 + ‖c‖) • (v : X)) - c = (1 + ‖c‖) • (v : X) := by abel
    rw [he, norm_smul, Real.norm_of_nonneg hU, v.property, mul_one] at h
    linarith
  have hcont : Continuous (fun t : ℝ => ‖c + t • (v : X)‖) :=
    (continuous_const.add (continuous_id.smul continuous_const)).norm
  obtain ⟨r, hr, hcontact⟩ :=
    intermediate_value_Icc hLU hcont.continuousOn ⟨hleft, hright⟩
  have hrpos : 0 < r := hL.trans_le hr.1
  refine ⟨r, ⟨hrpos, hcontact⟩, ?_⟩
  intro s hs
  exact contact_unique c hc (v : X) hs.1.le hrpos.le hs.2 hcontact

/-- The radius is chosen from the proved existence theorem. -/
def radialRadius (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) : ℝ :=
  Classical.choose (existsUnique_radialContact c hc v).exists

theorem radialRadius_spec (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    0 < radialRadius c hc v ∧ ‖c + radialRadius c hc v • (v : X)‖ = 1 :=
  Classical.choose_spec (existsUnique_radialContact c hc v).exists

theorem radialRadius_pos (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    0 < radialRadius c hc v := (radialRadius_spec c hc v).1

theorem norm_radialRadius (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    ‖c + radialRadius c hc v • (v : X)‖ = 1 := (radialRadius_spec c hc v).2

theorem radialRadius_bounds (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    1 - ‖c‖ ≤ radialRadius c hc v ∧ radialRadius c hc v ≤ 1 + ‖c‖ :=
  contact_bounds c v (radialRadius_pos c hc v).le (norm_radialRadius c hc v)

theorem radialRadius_unique (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X)
    {r : ℝ} (hr : 0 ≤ r) (hcontact : ‖c + r • (v : X)‖ = 1) :
    r = radialRadius c hc v :=
  contact_unique c hc (v : X) hr (radialRadius_pos c hc v).le
    hcontact (norm_radialRadius c hc v)

/-- The quantitative comparison for the chosen contact radii. -/
theorem radialRadius_comparison (c : X) (hc : ‖c‖ < 1) (v w : UnitSphere X) :
    (1 - ‖c‖) * |radialRadius c hc v - radialRadius c hc w| ≤
      (radialRadius c hc v * radialRadius c hc w) * ‖(v : X) - (w : X)‖ :=
  contact_comparison c (v : X) (w : X)
    (radialRadius_pos c hc v).le (radialRadius_pos c hc w).le
    (norm_radialRadius c hc v) (norm_radialRadius c hc w)

theorem radialRadius_sub_le (c : X) (hc : ‖c‖ < 1) (v w : UnitSphere X) :
    |radialRadius c hc v - radialRadius c hc w| ≤
      ((1 + ‖c‖)^2 / (1 - ‖c‖)) * ‖(v : X) - (w : X)‖ := by
  have hU : 0 ≤ 1 + ‖c‖ := by linarith [norm_nonneg c]
  have hproduct : radialRadius c hc v * radialRadius c hc w ≤ (1 + ‖c‖)^2 := by
    calc
      radialRadius c hc v * radialRadius c hc w ≤ (1 + ‖c‖) * radialRadius c hc w :=
        mul_le_mul_of_nonneg_right (radialRadius_bounds c hc v).2
          (radialRadius_pos c hc w).le
      _ ≤ (1 + ‖c‖) * (1 + ‖c‖) :=
        mul_le_mul_of_nonneg_left (radialRadius_bounds c hc w).2 hU
      _ = (1 + ‖c‖)^2 := by ring
  have hscaled : |radialRadius c hc v - radialRadius c hc w| * (1 - ‖c‖) ≤
      (1 + ‖c‖)^2 * ‖(v : X) - (w : X)‖ := by
    calc
      |radialRadius c hc v - radialRadius c hc w| * (1 - ‖c‖) =
          (1 - ‖c‖) * |radialRadius c hc v - radialRadius c hc w| := mul_comm _ _
      _ ≤ (radialRadius c hc v * radialRadius c hc w) * ‖(v : X) - (w : X)‖ :=
        radialRadius_comparison c hc v w
      _ ≤ (1 + ‖c‖)^2 * ‖(v : X) - (w : X)‖ :=
        mul_le_mul_of_nonneg_right hproduct (norm_nonneg _)
  calc
    |radialRadius c hc v - radialRadius c hc w| ≤
        ((1 + ‖c‖)^2 * ‖(v : X) - (w : X)‖) / (1 - ‖c‖) :=
      (le_div_iff₀ (sub_pos.mpr hc)).mpr hscaled
    _ = ((1 + ‖c‖)^2 / (1 - ‖c‖)) * ‖(v : X) - (w : X)‖ := by ring

/-- The radius is globally Lipschitz on the unit sphere for each fixed interior
center, even in an infinite-dimensional normed space. -/
theorem lipschitz_radialRadius (c : X) (hc : ‖c‖ < 1) :
    LipschitzWith (Real.toNNReal ((1 + ‖c‖)^2 / (1 - ‖c‖))) (radialRadius c hc) := by
  apply LipschitzWith.of_dist_le'
  intro v w
  simpa only [Real.dist_eq, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs] using radialRadius_sub_le c hc v w

theorem continuous_radialRadius (c : X) (hc : ‖c‖ < 1) :
    Continuous (radialRadius c hc) := (lipschitz_radialRadius c hc).continuous

/-- The actual point of contact, retaining its unit-sphere subtype proof. -/
def radialContact (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) : UnitSphere X :=
  ⟨c + radialRadius c hc v • (v : X), norm_radialRadius c hc v⟩

@[simp] theorem radialContact_coe (c : X) (hc : ‖c‖ < 1) (v : UnitSphere X) :
    (radialContact c hc v : X) = c + radialRadius c hc v • (v : X) := rfl

theorem continuous_radialContact (c : X) (hc : ‖c‖ < 1) :
    Continuous (radialContact c hc) :=
  (continuous_const.add ((continuous_radialRadius c hc).smul continuous_subtype_val)).subtype_mk _

end Tingley

end

end OAI
