import OAI.Geometry.CylinderCovering.Rational.Inversion
import OAI.Geometry.CylinderCovering.Rational.Field

namespace OAI

open Set

namespace SlopeRational

lemma tiltedMap_wall_plus (d s : ℝ) {p : Plane}
    (hden : radius (p 1) + d ≠ 0) :
    radius ((tiltedMap d s p) 1) / 2 + (tiltedMap d s p) 0 =
      (radius (p 1) / 2 + p 0) *
        (1 - s * ((2 * p 0 + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2))) := by
  simp only [tiltedMap, field, PiLp.add_apply, PiLp.smul_apply, vec2_zero, vec2_one,
    smul_eq_mul]
  rw [show radius (p 1 + s * b d (p 0) (p 1)) =
      radius (p 1) - s * b d (p 0) (p 1) by unfold radius; ring]
  unfold a b
  field_simp [hden]
  ring

lemma tiltedMap_wall_minus (d s : ℝ) {p : Plane}
    (hden : radius (p 1) + d ≠ 0) :
    radius ((tiltedMap d s p) 1) / 2 - (tiltedMap d s p) 0 =
      (radius (p 1) / 2 - p 0) *
        (1 + s * ((-2 * p 0 + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2))) := by
  simp only [tiltedMap, field, PiLp.add_apply, PiLp.smul_apply, vec2_zero, vec2_one,
    smul_eq_mul]
  rw [show radius (p 1 + s * b d (p 0) (p 1)) =
      radius (p 1) - s * b d (p 0) (p 1) by unfold radius; ring]
  unfold a b
  field_simp [hden]
  ring

lemma mem_wedge_iff_walls (p : Plane) :
    p ∈ wedge ↔ 0 ≤ radius (p 1) / 2 + p 0 ∧ 0 ≤ radius (p 1) / 2 - p 0 := by
  change 2 * |p 0| ≤ radius (p 1) ↔ _
  constructor
  · intro h
    constructor <;> linarith [le_abs_self (p 0), neg_le_abs (p 0)]
  · rintro ⟨hplus, hminus⟩
    have h : |p 0| ≤ radius (p 1) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

lemma rectangle_wall_coefficients_bounded {d : ℝ} (hd : 0 < d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ inverseRectangle d,
      |(2 * p 0 + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2)| ≤ M ∧
      |(-2 * p 0 + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2)| ≤ M := by
  have hplus : ContinuousOn (fun p : Plane =>
      (2 * p 0 + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2))
      (inverseRectangle d) := by
    apply ContinuousOn.div
    · unfold radius; fun_prop
    · unfold radius; fun_prop
    · intro p hp
      have := inverseRectangle_denominator_pos hd hp
      positivity
  have hminus : ContinuousOn (fun p : Plane =>
      (-2 * p 0 + 2 * d + radius (p 1)) / (8 * (radius (p 1) + d) ^ 2))
      (inverseRectangle d) := by
    apply ContinuousOn.div
    · unfold radius; fun_prop
    · unfold radius; fun_prop
    · intro p hp
      have := inverseRectangle_denominator_pos hd hp
      positivity
  obtain ⟨P, hP⟩ := (inverseRectangle_isCompact hd).exists_bound_of_continuousOn hplus
  obtain ⟨Q, hQ⟩ := (inverseRectangle_isCompact hd).exists_bound_of_continuousOn hminus
  refine ⟨max 0 (max P Q), le_max_left _ _, ?_⟩
  intro p hp
  constructor
  · exact (hP p hp).trans ((le_max_left P Q).trans (le_max_right 0 (max P Q)))
  · exact (hQ p hp).trans ((le_max_right P Q).trans (le_max_right 0 (max P Q)))

theorem rectangleWedge_main : RectangleWedgeStatement := by
  intro d hd
  obtain ⟨M, hM, hbound⟩ := rectangle_wall_coefficients_bounded hd
  have hMp : 0 < M + 1 := by positivity
  refine ⟨1 / (M + 1), div_pos (by norm_num) hMp, ?_⟩
  intro s hs p hp
  have hsM : |s| * M < 1 := by
    have hsm := (lt_div_iff₀ hMp).mp hs
    nlinarith [abs_nonneg s]
  obtain ⟨hplus, hminus⟩ := hbound p hp
  have hplusabs : |s * ((2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2))| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hplus (abs_nonneg _)).trans_lt hsM
  have hminusabs : |s * ((-2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2))| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hminus (abs_nonneg _)).trans_lt hsM
  have hfactorplus : 0 < 1 - s * ((2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2)) := by
    have := (abs_lt.mp hplusabs).2
    linarith
  have hfactorminus : 0 < 1 + s * ((-2 * p 0 + 2 * d + radius (p 1)) /
      (8 * (radius (p 1) + d) ^ 2)) := by
    have := (abs_lt.mp hminusabs).1
    linarith
  have hden := ne_of_gt (inverseRectangle_denominator_pos hd hp)
  rw [mem_wedge_iff_walls, mem_wedge_iff_walls,
    tiltedMap_wall_plus d s hden, tiltedMap_wall_minus d s hden]
  exact and_congr (mul_nonneg_iff_of_pos_right hfactorplus)
    (mul_nonneg_iff_of_pos_right hfactorminus)

theorem uniform_wedge_inverse {d : ℝ} (hd : 0 < d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      ∀ y t : ℝ, |y| ≤ 1 / 2 → |t| ≤ 1 / 2 → vec2 y t ∈ wedge →
        ∃! p : Plane,
          p ∈ inverseRectangle d ∧ p ∈ wedge ∧ tiltedMap d s p = vec2 y t := by
  obtain ⟨δ₁, hδ₁, hinverse⟩ := rectangleInversion_main d hd
  obtain ⟨δ₂, hδ₂, hwedge⟩ := rectangleWedge_main d hd
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro s hs y t hy ht htarget
  have hs₁ := lt_of_lt_of_le hs (min_le_left δ₁ δ₂)
  have hs₂ := lt_of_lt_of_le hs (min_le_right δ₁ δ₂)
  obtain ⟨p, hp, huni⟩ := (hinverse s hs₁).1 y t hy ht
  have hpw : p ∈ wedge := (hwedge s hs₂ p hp.1).mp (by rwa [hp.2])
  refine ⟨p, ⟨hp.1, hpw, hp.2⟩, ?_⟩
  intro q hq
  exact huni q ⟨hq.1, hq.2.2⟩

end SlopeRational

end OAI
