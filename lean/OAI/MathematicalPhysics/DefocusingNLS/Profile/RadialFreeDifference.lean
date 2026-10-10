import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeLinearTaylor

namespace OAI

/-! Dependence on the starting radius, proved by comparing actual integral solutions. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radial_free_start_difference (b l₁ l₂ u : ℝ)
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
      -radialFreeCoefficient t*G₂ t-(b : ℂ)*F₂ t)
    (hB₁ : ∀ r ∈ Icc l₁ u, ‖F₁ r‖ ≤ 2 ∧ ‖G₁ r‖ ≤ 2) :
    ∀ r ∈ Icc l₂ u,
      ‖F₁ r-F₂ r+(b : ℂ)/2*((l₂-l₁ : ℝ) : ℂ)^2+
        (b : ℂ)*((l₂-l₁ : ℝ) : ℂ)*((r-l₂ : ℝ) : ℂ)‖ ≤
          (6/1000 : ℝ)*(l₂-l₁)*(r-l₁) := by
  have h₁u : l₁ ≤ u := h₁₂.trans h₂u
  have hl₂ : (3 : ℝ) ≤ l₂ := hl.trans h₁₂
  have hw₂ : u-l₂ ≤ (1/1000 : ℝ) := by linarith
  have hstate₁ := radial_free_components_state b l₁ u (by linarith) F₁ G₁ hF₁ hG₁ 1 0
    heF₁ (by simpa only [zero_add] using heG₁)
  have hstate₂ := radial_free_components_state b l₂ u (by linarith) F₂ G₂ hF₂ hG₂ 1 0
    heF₂ (by simpa only [zero_add] using heG₂)
  have hre := radial_free_state_restart b l₁ u l₂ (by linarith) ⟨h₁₂,h₂u⟩
    (fun t => (F₁ t,G₁ t)) (hF₁.prodMk hG₁) (1,0) hstate₁
  have hsub := radial_free_state_sub b l₂ u (by linarith)
    (fun t => (F₁ t,G₁ t)) (fun t => (F₂ t,G₂ t))
    (hF₁.prodMk hG₁) (hF₂.prodMk hG₂) (F₁ l₂,G₁ l₂) (1,0) hre hstate₂
  have hcomp := radial_free_state_components b l₂ u (by linarith)
    (fun t => (F₁ t,G₁ t)-(F₂ t,G₂ t)) ((hF₁.prodMk hG₁).sub (hF₂.prodMk hG₂))
    ((F₁ l₂,G₁ l₂)-(1,0)) hsub
  have hlin := radial_free_linear_taylor b l₂ u hb hl₂ hu h₂u hw₂
    (fun t => F₁ t-F₂ t) (fun t => G₁ t-G₂ t) (hF₁.sub hF₂) (hG₁.sub hG₂)
    (F₁ l₂-1) (G₁ l₂) hcomp.1 (by simpa only [Prod.fst_sub,Prod.snd_sub,sub_zero] using hcomp.2)
  have hT := radial_free_taylor b l₁ u hb hl hu h₁u hwidth F₁ G₁ hF₁ hG₁ heF₁ heG₁ hB₁ l₂ ⟨h₁₂,h₂u⟩
  have hs := radial_free_short_bounds b l₁ u hb hl hu h₁u hwidth F₁ G₁ heF₁ heG₁ hB₁ l₂ ⟨h₁₂,h₂u⟩
  have hδ : 0 ≤ l₂-l₁ := sub_nonneg.mpr h₁₂
  have hδu : l₂-l₁ ≤ (1/1000 : ℝ) := by linarith
  have hN : ‖(F₁ l₂-1,G₁ l₂)‖ ≤ (35/100 : ℝ)*(l₂-l₁) := by
    rw [Prod.norm_mk]
    apply max_le _ hs.1
    have hsq := mul_le_mul_of_nonneg_left hδu hδ
    nlinarith [hs.2]
  intro r hr
  have hv : 0 ≤ r-l₂ := sub_nonneg.mpr hr.1
  have hvu : r-l₂ ≤ (1/1000 : ℝ) := by linarith [hr.2]
  have he : F₁ r-F₂ r+(b : ℂ)/2*((l₂-l₁ : ℝ) : ℂ)^2+
      (b : ℂ)*((l₂-l₁ : ℝ) : ℂ)*((r-l₂ : ℝ) : ℂ)=
      (F₁ r-F₂ r-(F₁ l₂-1)-G₁ l₂*((r-l₂ : ℝ) : ℂ))+
        (F₁ l₂-1+(b : ℂ)/2*((l₂-l₁ : ℝ) : ℂ)^2)+
        (G₁ l₂+(b : ℂ)*((l₂-l₁ : ℝ) : ℂ))*((r-l₂ : ℝ) : ℂ) := by ring
  rw [he]
  have hgn : ‖(G₁ l₂+(b : ℂ)*((l₂-l₁ : ℝ) : ℂ))*((r-l₂ : ℝ) : ℂ)‖ ≤
      (3/1000 : ℝ)*(l₂-l₁)*(r-l₂) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv]
    exact mul_le_mul_of_nonneg_right hT.1 hv
  have hh : ‖(F₁ r-F₂ r-(F₁ l₂-1)-G₁ l₂*((r-l₂ : ℝ) : ℂ))+
        (F₁ l₂-1+(b : ℂ)/2*((l₂-l₁ : ℝ) : ℂ)^2)+
        (G₁ l₂+(b : ℂ)*((l₂-l₁ : ℝ) : ℂ))*((r-l₂ : ℝ) : ℂ)‖ ≤
      7*‖(F₁ l₂-1,G₁ l₂)‖*(r-l₂)^2+(3/2000 : ℝ)*(l₂-l₁)^2+
        (3/1000 : ℝ)*(l₂-l₁)*(r-l₂) :=
    (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (hlin r hr).2 hT.2)) hgn)
  have hn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ) ≤ 7)) (sq_nonneg (r-l₂))
  have hvv : (r-l₂)^2 ≤ (r-l₂)/1000 := by nlinarith [mul_le_mul_of_nonneg_left hvu hv]
  have hprod := mul_le_mul_of_nonneg_left hvv hδ
  nlinarith

end DefocusingNLS

end OAI
