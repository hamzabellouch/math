import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeParameterBound

namespace OAI

/-! Lipschitz dependence of the actual endpoint jet on the starting radius and coefficient. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_free_endpoint_difference_of_le (b c l₁ l₂ u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l₁)
    (hu : u ≤ (10/3 : ℝ)) (h₁₂ : l₁ ≤ l₂) (h₂u : l₂ ≤ u)
    (hwidth : u-l₁ ≤ (1/1000 : ℝ))
    (F₁ G₁ F₂ G₂ : ℝ → ℂ)
    (hF₁ : Continuous F₁) (hG₁ : Continuous G₁)
    (hF₂ : Continuous F₂) (hG₂ : Continuous G₂)
    (heF₁ : ∀ r ∈ Icc l₁ u, F₁ r=1+∫ t in l₁..r, G₁ t)
    (heG₁ : ∀ r ∈ Icc l₁ u, G₁ r=∫ t in l₁..r,
      -radialFreeCoefficient t*G₁ t-(b : ℂ)*F₁ t)
    (heF₂ : ∀ r ∈ Icc l₂ u, F₂ r=1+∫ t in l₂..r, G₂ t)
    (heG₂ : ∀ r ∈ Icc l₂ u, G₂ r=∫ t in l₂..r,
      -radialFreeCoefficient t*G₂ t-(c : ℂ)*F₂ t)
    (hB₁ : ∀ r ∈ Icc l₁ u, ‖F₁ r‖ ≤ 2 ∧ ‖G₁ r‖ ≤ 2)
    (hB₂ : ∀ r ∈ Icc l₂ u, ‖F₂ r‖ ≤ 2 ∧ ‖G₂ r‖ ≤ 2) :
    ‖(F₁ u,G₁ u)-(F₂ u,G₂ u)‖ ≤ (l₂-l₁)+|b-c| := by
  have h₁u := h₁₂.trans h₂u
  have hl₂ := hl.trans h₁₂
  have hw₂ : u-l₂ ≤ (1/1000 : ℝ) := by linarith
  have hstate₁ := radial_free_components_state b l₁ u (by linarith) F₁ G₁ hF₁ hG₁ 1 0
    heF₁ (by simpa only [zero_add] using heG₁)
  have hstate₂ := radial_free_components_state c l₂ u (by linarith) F₂ G₂ hF₂ hG₂ 1 0
    heF₂ (by simpa only [zero_add] using heG₂)
  have hre := radial_free_state_restart b l₁ u l₂ (by linarith) ⟨h₁₂,h₂u⟩
    (fun t => (F₁ t,G₁ t)) (hF₁.prodMk hG₁) (1,0) hstate₁
  have hd := radial_free_state_parameter_bound b c l₂ u hb hl₂ hu h₂u hw₂
    (fun t => (F₁ t,G₁ t)) (fun t => (F₂ t,G₂ t))
    (hF₁.prodMk hG₁) (hF₂.prodMk hG₂) (F₁ l₂,G₁ l₂) (1,0) hre hstate₂
    (fun r hr => by rw [Prod.norm_mk]; exact max_le (hB₂ r hr).1 (hB₂ r hr).2)
    u ⟨h₂u,le_rfl⟩
  have hs := radial_free_short_bounds b l₁ u hb hl hu h₁u hwidth F₁ G₁ heF₁ heG₁ hB₁ l₂ ⟨h₁₂,h₂u⟩
  have hδ : 0 ≤ l₂-l₁ := sub_nonneg.mpr h₁₂
  have hδu : l₂-l₁ ≤ (1/1000 : ℝ) := by linarith
  have hN : ‖(F₁ l₂,G₁ l₂)-(1,0)‖ ≤ (35/100 : ℝ)*(l₂-l₁) := by
    change max ‖F₁ l₂-1‖ ‖G₁ l₂-0‖ ≤ _
    rw [sub_zero]
    apply max_le _ hs.1
    have hsq := mul_le_mul_of_nonneg_left hδu hδ
    nlinarith [hs.2]
  linarith

theorem radial_free_endpoint_difference (b c l₁ l₂ u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hc : c ∈ Icc (334/1000 : ℝ) (335/1000))
    (hl₁ : (3 : ℝ) ≤ l₁) (hl₂ : (3 : ℝ) ≤ l₂) (hu : u ≤ (10/3 : ℝ))
    (h₁u : l₁ ≤ u) (h₂u : l₂ ≤ u)
    (hw₁ : u-l₁ ≤ (1/1000 : ℝ)) (hw₂ : u-l₂ ≤ (1/1000 : ℝ))
    (F₁ G₁ F₂ G₂ : ℝ → ℂ)
    (hF₁ : Continuous F₁) (hG₁ : Continuous G₁)
    (hF₂ : Continuous F₂) (hG₂ : Continuous G₂)
    (heF₁ : ∀ r ∈ Icc l₁ u, F₁ r=1+∫ t in l₁..r, G₁ t)
    (heG₁ : ∀ r ∈ Icc l₁ u, G₁ r=∫ t in l₁..r,
      -radialFreeCoefficient t*G₁ t-(b : ℂ)*F₁ t)
    (heF₂ : ∀ r ∈ Icc l₂ u, F₂ r=1+∫ t in l₂..r, G₂ t)
    (heG₂ : ∀ r ∈ Icc l₂ u, G₂ r=∫ t in l₂..r,
      -radialFreeCoefficient t*G₂ t-(c : ℂ)*F₂ t)
    (hB₁ : ∀ r ∈ Icc l₁ u, ‖F₁ r‖ ≤ 2 ∧ ‖G₁ r‖ ≤ 2)
    (hB₂ : ∀ r ∈ Icc l₂ u, ‖F₂ r‖ ≤ 2 ∧ ‖G₂ r‖ ≤ 2) :
    ‖(F₁ u,G₁ u)-(F₂ u,G₂ u)‖ ≤ |l₁-l₂|+|b-c| := by
  rcases le_total l₁ l₂ with hle | hle
  · have hh := radial_free_endpoint_difference_of_le b c l₁ l₂ u hb hl₁ hu hle h₂u hw₁
      F₁ G₁ F₂ G₂ hF₁ hG₁ hF₂ hG₂ heF₁ heG₁ heF₂ heG₂ hB₁ hB₂
    simpa only [abs_sub_comm l₁ l₂,abs_of_nonneg (sub_nonneg.mpr hle)] using hh
  · have hh := radial_free_endpoint_difference_of_le c b l₂ l₁ u hc hl₂ hu hle h₁u hw₂
      F₂ G₂ F₁ G₁ hF₂ hG₂ hF₁ hG₁ heF₂ heG₂ heF₁ heG₁ hB₂ hB₁
    simpa only [norm_sub_rev (F₂ u,G₂ u),abs_sub_comm c b,
      abs_of_nonneg (sub_nonneg.mpr hle)] using hh

end DefocusingNLS

end OAI
