import OAI.MeasureTheory.Falconer.Slicing.PlanarSliceGeometry

namespace OAI

/-! # Direction-ball control transfers to the slope coordinate -/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem normalize_dist_le_twice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {x y : E} (hx : 1 ≤ ‖x‖) (hy : y ≠ 0) :
    dist (normalize x) (normalize y) ≤ 2*dist x y := by
  have he : ‖x‖ • (normalize x-normalize y) =
      x-y+(‖y‖-‖x‖) • normalize y := by
    rw [smul_sub,norm_smul_normalize,sub_smul,norm_smul_normalize]
    abel
  have hb := norm_add_le (x-y) ((‖y‖-‖x‖) • normalize y)
  rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),
    norm_smul,Real.norm_eq_abs,norm_normalize hy,mul_one] at hb
  have hn := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at hn
  rw [dist_eq_norm,dist_eq_norm]
  nlinarith [norm_nonneg (normalize x-normalize y)]

noncomputable def slopeVector (m : ℝ) : Space 2 := WithLp.toLp 2 ![1,m]

@[simp] theorem slopeVector_zero (m : ℝ) : slopeVector m 0 = 1 := rfl
@[simp] theorem slopeVector_one (m : ℝ) : slopeVector m 1 = m := rfl

theorem slopeVector_norm_lower (m : ℝ) : 1 ≤ ‖slopeVector m‖ := by
  simpa only [slopeVector_zero,Real.norm_eq_abs,abs_one] using
    PiLp.norm_apply_le (slopeVector m) 0

theorem slopeVector_dist (m t : ℝ) : dist (slopeVector m) (slopeVector t) = |m-t| := by
  have hh := EuclideanSpace.dist_sq_eq (slopeVector m) (slopeVector t)
  simp only [Fin.sum_univ_two,slopeVector_zero,slopeVector_one,Real.dist_eq,sq_abs,sub_self,
    zero_pow (by omega : 2 ≠ 0),zero_add] at hh
  nlinarith [dist_nonneg (x := slopeVector m) (y := slopeVector t),abs_nonneg (m-t),sq_abs (m-t)]

theorem slopeDirection_dist (m t : ℝ) :
    dist (normalize (slopeVector m)) (normalize (slopeVector t)) ≤ 2*|m-t| := by
  have ht : slopeVector t ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one (slopeVector_norm_lower t))
  simpa only [slopeVector_dist] using normalize_dist_le_twice (slopeVector_norm_lower m) ht

theorem planar_unit_eq_slopeDirection {w : Space 2} (hw : ‖w‖ = 1) (hpos : 0 < w 0) :
    w = normalize (slopeVector (planarSlope w)) := by
  have he : w = w 0 • slopeVector (planarSlope w) := by
    apply PiLp.ext
    intro i
    fin_cases i
    · change w 0 = w 0 * 1
      ring
    · change w 1 = w 0 * (w 1 / w 0)
      field_simp
  have hn := normalize_eq_self_of_norm_eq_one hw
  rw [he,normalize_smul_of_pos hpos] at hn
  exact he.trans hn.symm

theorem planar_slope_ball_subset {W : Type*} (q : W → Space 2)
    (hunit : ∀ w, ‖q w‖ = 1) (hpos : ∀ w, 0 < q w 0) (a r : ℝ) :
    {w | |planarSlope (q w)-a| ≤ r} ⊆
      {w | dist (q w) (normalize (slopeVector a)) ≤ 2*r} := by
  intro w hw
  change dist (q w) (normalize (slopeVector a)) ≤ 2*r
  rw [planar_unit_eq_slopeDirection (hunit w) (hpos w)]
  exact (slopeDirection_dist _ a).trans (mul_le_mul_of_nonneg_left hw (by norm_num))

theorem planar_slope_ball_measure {W : Type*} [MeasurableSpace W]
    (ν : Measure W) (q : W → Space 2)
    (hunit : ∀ w, ‖q w‖ = 1) (hpos : ∀ w, 0 < q w 0) (a r : ℝ) :
    ν {w | |planarSlope (q w)-a| ≤ r} ≤
      ν {w | dist (q w) (normalize (slopeVector a)) ≤ 2*r} :=
  measure_mono (planar_slope_ball_subset q hunit hpos a r)

end Falconer

end OAI
