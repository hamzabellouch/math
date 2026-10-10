import OAI.Geometry.CylinderCovering.Rational.GlobalInversion

namespace OAI

noncomputable section

open Set
open scoped NNReal

namespace SlopeRational

theorem global_displacement_lipschitz {d s : ℝ} (hd : 0 < d)
    {p q : Plane} (hp : p ∈ wedge) (hq : q ∈ wedge) :
    ‖s • field d p - s • field d q‖ ≤
      (|s| * (2 / d)) * ‖p - q‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  have h := (field_lipschitzOn_wedge hd).dist_le_mul p hp q hq
  change dist (field d p) (field d q) ≤ (2 / d) * dist p q at h
  rw [dist_eq_norm, dist_eq_norm] at h
  calc
    |s| * ‖field d p - field d q‖ ≤ |s| * ((2 / d) * ‖p - q‖) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by ring

theorem global_tiltedMap_metric_bounds {d s : ℝ} (hd : 0 < d)
    {p q : Plane} (hp : p ∈ wedge) (hq : q ∈ wedge) :
    (1 - |s| * (2 / d)) * ‖p - q‖ ≤
        ‖tiltedMap d s p - tiltedMap d s q‖ ∧
      ‖tiltedMap d s p - tiltedMap d s q‖ ≤
        (1 + |s| * (2 / d)) * ‖p - q‖ := by
  have hdisp := global_displacement_lipschitz hd hp hq (s := s)
  have heq : tiltedMap d s p - tiltedMap d s q =
      (p - q) + (s • field d p - s • field d q) := by
    simp only [tiltedMap]
    abel
  have hu := norm_add_le (p - q) (s • field d p - s • field d q)
  have hl := norm_sub_le (tiltedMap d s p - tiltedMap d s q)
    (s • field d p - s • field d q)
  rw [heq, add_sub_cancel_right] at hl
  rw [heq]
  constructor <;> nlinarith

theorem global_tiltedMap_uniform_metric_bounds {d s : ℝ} (hd : 0 < d)
    (hs : |s| < d / 4) {p q : Plane} (hp : p ∈ wedge) (hq : q ∈ wedge) :
    ‖p - q‖ ≤ 2 * ‖tiltedMap d s p - tiltedMap d s q‖ ∧
      ‖tiltedMap d s p - tiltedMap d s q‖ ≤ (3 / 2 : ℝ) * ‖p - q‖ := by
  have hc : |s| * (2 / d) < 1 / 2 := by
    rw [show |s| * (2 / d) = (2 * |s|) / d by ring]
    apply (div_lt_iff₀ hd).2
    linarith
  obtain ⟨hl, hu⟩ := global_tiltedMap_metric_bounds hd hp hq (s := s)
  have hnorm := norm_nonneg (p - q)
  constructor <;> nlinarith

theorem global_wall_factors_pos {d s : ℝ} (hd : 0 < d) (hs : |s| < d)
    {p : Plane} (hp : p ∈ wedge) :
    0 < 1 - s * ((2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2)) ∧
    0 < 1 + s * ((-2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2)) := by
  obtain ⟨hplus, hminus⟩ := global_wall_coefficients hd hp
  have hsmall : |s| * (1 / (4 * d)) < 1 := by
    rw [mul_one_div]
    apply (div_lt_one (by positivity : 0 < 4 * d)).2
    linarith [abs_nonneg s]
  have hap : |s * ((2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2))| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hplus (abs_nonneg _)).trans_lt hsmall
  have ham : |s * ((-2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2))| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hminus (abs_nonneg _)).trans_lt hsmall
  exact ⟨by linarith [(abs_lt.mp hap).2], by linarith [(abs_lt.mp ham).1]⟩

theorem global_wall_zero_iff {d s : ℝ} (hd : 0 < d) (hs : |s| < d)
    {p : Plane} (hp : p ∈ wedge) :
    (radius ((tiltedMap d s p) 1) / 2 + (tiltedMap d s p) 0 = 0 ↔
      radius (p 1) / 2 + p 0 = 0) ∧
    (radius ((tiltedMap d s p) 1) / 2 - (tiltedMap d s p) 0 = 0 ↔
      radius (p 1) / 2 - p 0 = 0) := by
  obtain ⟨hpplus, hpminus⟩ := global_wall_factors_pos hd hs hp
  have hden := (denominator_pos_of_mem_wedge hd hp).ne'
  rw [tiltedMap_wall_plus d s hden, tiltedMap_wall_minus d s hden]
  simp only [mul_eq_zero, ne_of_gt hpplus, ne_of_gt hpminus, or_false,
    iff_self, and_self]

theorem global_wall_pos_iff {d s : ℝ} (hd : 0 < d) (hs : |s| < d)
    {p : Plane} (hp : p ∈ wedge) :
    (0 < radius ((tiltedMap d s p) 1) / 2 + (tiltedMap d s p) 0 ↔
      0 < radius (p 1) / 2 + p 0) ∧
    (0 < radius ((tiltedMap d s p) 1) / 2 - (tiltedMap d s p) 0 ↔
      0 < radius (p 1) / 2 - p 0) := by
  obtain ⟨hpplus, hpminus⟩ := global_wall_factors_pos hd hs hp
  have hden := (denominator_pos_of_mem_wedge hd hp).ne'
  rw [tiltedMap_wall_plus d s hden, tiltedMap_wall_minus d s hden]
  exact ⟨mul_pos_iff_of_pos_right hpplus, mul_pos_iff_of_pos_right hpminus⟩

theorem global_wedge_homeomorphism {d s : ℝ} (hd : 0 < d) (hs : |s| < d / 4) :
    ∃ F : wedge ≃ₜ wedge,
      (∀ p : wedge, (F p : Plane) = tiltedMap d s p) ∧
      LipschitzWith (3 / 2 : ℝ≥0) F ∧ LipschitzWith 2 F.symm := by
  have hmap := global_tiltedMap_mapsTo hd (s := s) (by linarith)
  let f : wedge → wedge := hmap.restrict (tiltedMap d s) wedge wedge
  have hlip : LipschitzWith (3 / 2 : ℝ≥0) f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    change dist (tiltedMap d s p) (tiltedMap d s q) ≤
      ((3 / 2 : ℝ≥0) : ℝ) * dist (p : Plane) (q : Plane)
    simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_ofNat] using
      (global_tiltedMap_uniform_metric_bounds hd hs p.property q.property).2
  have hanti : AntilipschitzWith 2 f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro p q
    change dist (p : Plane) (q : Plane) ≤
      ((2 : ℝ≥0) : ℝ) * dist (tiltedMap d s p) (tiltedMap d s q)
    simpa only [dist_eq_norm, NNReal.coe_ofNat] using
      (global_tiltedMap_uniform_metric_bounds hd hs p.property q.property).1
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨p, hp, _⟩ := rational_global_inverse hd hs y.property
    exact ⟨⟨p, hp.1⟩, Subtype.ext hp.2⟩
  let F := (hanti.isEmbedding hlip.continuous).toHomeomorphOfSurjective hsurj
  refine ⟨F, fun p => rfl, hlip, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := hanti.le_mul_dist (F.symm p) (F.symm q)
  change dist (F.symm p) (F.symm q) ≤
    ((2 : ℝ≥0) : ℝ) * dist (F (F.symm p)) (F (F.symm q)) at h
  simpa only [Homeomorph.apply_symm_apply] using h

theorem rational_global_inverse_uniform {d ε : ℝ} (hd : 0 < d)
    (hε : |ε| < d / 2) {x : ℝ} (hx : |x| ≤ 1 / 2)
    {y : Plane} (hy : y ∈ wedge) :
    ∃! p : Plane, p ∈ wedge ∧ tiltedMap d (ε * x) p = y := by
  apply rational_global_inverse hd ?_ hy
  rw [abs_mul]
  have hbound := mul_le_mul_of_nonneg_left hx (abs_nonneg ε)
  linarith

end SlopeRational

end

end OAI
