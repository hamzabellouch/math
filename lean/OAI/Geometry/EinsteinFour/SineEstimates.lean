import OAI.Geometry.EinsteinFour.VolumeConstants
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace OAI

/-! The analytic comparison underlying the rational radial integrals. The
alternating seventh-degree sine bound is proved by successive derivatives,
then compared with the exact rational polynomial used in `VolumeConstants`. -/

namespace PositiveEinsteinFour.VolumeConstants

noncomputable section

private theorem nonneg_of_derivative {f d : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (d x) x)
    (hd0 : ∀ x, 0 ≤ x → 0 ≤ d x) (hf0 : 0 ≤ f 0) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
    · intro x _
      exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hd x).deriv]
      exact hd0 x hx.le
  exact hf0.trans (hmono (by simp) hx hx)

private theorem cos_fourth_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hd (t : ℝ) : HasDerivAt (fun z => 1 - z ^ 2 / 2 + z ^ 4 / 24 - Real.cos z)
      (Real.sin t - t + t ^ 3 / 6) t := by
    convert (((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 4).div_const 24)).sub (Real.hasDerivAt_cos t) using 1
    all_goals first | rfl | (try simp only [id_eq]; ring)
  have h := nonneg_of_derivative hd (fun t ht => by linarith [Real.sin_ge_sub_cube ht])
    (by norm_num) hx
  linarith

private theorem sin_fifth_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hd (t : ℝ) : HasDerivAt (fun z => z - z ^ 3 / 6 + z ^ 5 / 120 - Real.sin z)
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t) t := by
    convert (((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 6)).add
      (((hasDerivAt_id t).pow 5).div_const 120)).sub (Real.hasDerivAt_sin t) using 1
    all_goals first | rfl | (try simp only [id_eq]; ring)
  have h := nonneg_of_derivative hd (fun t ht => by linarith [cos_fourth_upper ht])
    (by norm_num) hx
  linarith

private theorem cos_sixth_lower {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have hd (t : ℝ) : HasDerivAt
      (fun z => Real.cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24 - z ^ 6 / 720))
      (t - t ^ 3 / 6 + t ^ 5 / 120 - Real.sin t) t := by
    convert (Real.hasDerivAt_cos t).sub ((((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 4).div_const 24)).sub
      (((hasDerivAt_id t).pow 6).div_const 720)) using 1
    all_goals first | rfl | (try simp only [id_eq]; ring)
  have h := nonneg_of_derivative hd (fun t ht => by linarith [sin_fifth_upper ht])
    (by norm_num) hx
  linarith

theorem sin_seventh_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := by
  have hd (t : ℝ) : HasDerivAt
      (fun z => Real.sin z - (z - z ^ 3 / 6 + z ^ 5 / 120 - z ^ 7 / 5040))
      (Real.cos t - (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720)) t := by
    convert (Real.hasDerivAt_sin t).sub ((((hasDerivAt_id t).sub
      (((hasDerivAt_id t).pow 3).div_const 6)).add
      (((hasDerivAt_id t).pow 5).div_const 120)).sub
      (((hasDerivAt_id t).pow 7).div_const 5040)) using 1
    all_goals first | rfl | (try simp only [id_eq]; ring)
  have h := nonneg_of_derivative hd (fun t ht => by linarith [cos_sixth_lower ht])
    (by norm_num) hx
  linarith

/-- The lower polynomial in the paper is below the sine of the true angle. -/
theorem sineLower_le_sin {z : ℝ} (hz : 0 ≤ z) : sineLower z ≤ Real.sin (Real.pi * z) := by
  have hpi0 : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hpi1 : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hsmall : (157 / 50 : ℝ) * z ≤ Real.pi * z := mul_le_mul_of_nonneg_right hpi0 hz
  have hlarge : Real.pi * z ≤ (22 / 7 : ℝ) * z := mul_le_mul_of_nonneg_right hpi1 hz
  have hpoly : sineLower z = (157 / 50 * z) - (22 / 7 * z) ^ 3 / 6 +
      (157 / 50 * z) ^ 5 / 120 - (22 / 7 * z) ^ 7 / 5040 := by
    unfold sineLower
    ring
  rw [hpoly]
  calc
    _ ≤ (Real.pi * z) - (Real.pi * z) ^ 3 / 6 +
        (Real.pi * z) ^ 5 / 120 - (Real.pi * z) ^ 7 / 5040 := by
      gcongr
    _ ≤ Real.sin (Real.pi * z) := sin_seventh_lower (mul_nonneg Real.pi_pos.le hz)

/-- Positivity of the same lower polynomial on the half interval used in the
reflection argument. -/
theorem sineLower_linear {z : ℝ} (hz : 0 ≤ z) (hz2 : z ≤ 1 / 2) :
    (9 / 5) * z ≤ sineLower z := by
  have hsquare : z ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hsix : z ^ 6 ≤ (1 / 64 : ℝ) := by
    have h := pow_le_pow_left₀ (sq_nonneg z) hsquare 3
    nlinarith only [h]
  have hcoefficient : (9 / 5 : ℝ) ≤
      157 / 50 - (22 / 7) ^ 3 * z ^ 2 / 6 +
        (157 / 50) ^ 5 * z ^ 4 / 120 - (22 / 7) ^ 7 * z ^ 6 / 5040 := by
    nlinarith only [hsquare, hsix, pow_nonneg hz 4]
  have h := mul_le_mul_of_nonneg_left hcoefficient hz
  unfold sineLower
  nlinarith only [h]

theorem sineLower_nonneg {z : ℝ} (hz : 0 ≤ z) (hz2 : z ≤ 1 / 2) :
    0 ≤ sineLower z := (by positivity : 0 ≤ (9 / 5 : ℝ) * z).trans (sineLower_linear hz hz2)

/-- Reflection makes the positive polynomial bound available on all of [0,1]. -/
theorem reflected_sineLower {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ sineLower (min u (1 - u)) ∧
      sineLower (min u (1 - u)) ≤ Real.sin (Real.pi * u) := by
  by_cases hh : u ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    exact ⟨sineLower_nonneg hu hh, sineLower_le_sin hu⟩
  · rw [min_eq_right (by linarith)]
    have hnonneg : 0 ≤ 1 - u := by linarith
    refine ⟨sineLower_nonneg hnonneg (by linarith), ?_⟩
    have h := sineLower_le_sin hnonneg
    rwa [mul_sub, mul_one, Real.sin_pi_sub] at h

end

end PositiveEinsteinFour.VolumeConstants

end OAI
