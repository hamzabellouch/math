import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialModulusComparison

namespace OAI

/-! The free endpoint modulus strictly increases with its starting radius. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_free_boundary_strict_mono (b l₁ l₂ u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l₁)
    (hu : u ≤ (10/3 : ℝ)) (h₁₂ : l₁ < l₂) (h₂u : l₂ ≤ u)
    (hwidth : u-l₁ ≤ (1/1000 : ℝ))
    (F₁ G₁ F₂ G₂ : ℝ → ℂ)
    (hF₁ : Continuous F₁) (hG₁ : Continuous G₁)
    (hF₂ : Continuous F₂) (hG₂ : Continuous G₂)
    (heF₁ : ∀ r ∈ Icc l₁ u, F₁ r=1+∫ t in l₁..r, G₁ t)
    (heG₁ : ∀ r ∈ Icc l₁ u, G₁ r=∫ t in l₁..r,
      -radialFreeCoefficient t*G₁ t-(b : ℂ)*F₁ t)
    (heF₂ : ∀ r ∈ Icc l₂ u, F₂ r=1+∫ t in l₂..r, G₂ t)
    (heG₂ : ∀ r ∈ Icc l₂ u, G₂ r=∫ t in l₂..r,
      -radialFreeCoefficient t*G₂ t-(b : ℂ)*F₂ t)
    (hB₁ : ∀ r ∈ Icc l₁ u, ‖F₁ r‖ ≤ 2 ∧ ‖G₁ r‖ ≤ 2)
    (hB₂ : ∀ r ∈ Icc l₂ u, ‖F₂ r‖ ≤ 2 ∧ ‖G₂ r‖ ≤ 2) :
    ‖F₁ u‖ < ‖F₂ u‖ := by
  have hδ : 0 < l₂-l₁ := sub_pos.mpr h₁₂
  have hv : 0 ≤ u-l₂ := sub_nonneg.mpr h₂u
  have hs : 0 < u-l₁ := by linarith
  have hδsmall : l₂-l₁ ≤ (1/1000 : ℝ) := by linarith
  have hx : 0 < (l₂-l₁)*(u-l₁) := mul_pos hδ hs
  have hxsmall : (l₂-l₁)*(u-l₁) ≤ (1/1000 : ℝ) := by
    have hh := mul_le_mul hδsmall hwidth hs.le (by norm_num : (0 : ℝ) ≤ 1/1000)
    nlinarith
  have he := radial_free_start_difference b l₁ l₂ u hb hl hu h₁₂.le h₂u hwidth
    F₁ G₁ F₂ G₂ hF₁ hG₁ hF₂ hG₂ heF₁ heG₁ heF₂ heG₂ hB₁ u ⟨h₂u,le_rfl⟩
  have hd := radial_free_difference_direction b (l₂-l₁) (u-l₂) (F₁ u-F₂ u) hb hδ.le hv
    (by convert he using 1; ring)
  have hw₂ : u-l₂ ≤ (1/1000 : ℝ) := by linarith
  have hf := (radial_free_short_bounds b l₂ u hb (hl.trans h₁₂.le) hu h₂u hw₂
    F₂ G₂ heF₂ heG₂ hB₂ u ⟨h₂u,le_rfl⟩).2
  have hnear : ‖F₂ u-1‖ ≤ (1/1000 : ℝ) := by
    have hh := pow_le_pow_left₀ hv hw₂ 2
    nlinarith
  have hdec := complex_norm_decrease_of_small_left_direction (F₂ u) (F₁ u-F₂ u)
    ((l₂-l₁)*(u-l₁)) hx hxsmall hnear
    (by convert hd.1 using 1; ring) (by convert hd.2 using 1; ring)
  simpa only [add_sub_cancel] using hdec

end DefocusingNLS

end OAI
