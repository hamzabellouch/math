import OAI.Geometry.CylinderCovering.Angular.CartesianDirect
import OAI.Geometry.CylinderCovering.Angular.CartesianObstruction

namespace OAI

namespace AngularCartesianDirect
open CylinderCovering.CartesianCaps

theorem selected_pair_domains {τ η M x y s l₁ r₁ l₂ r₂ S T : ℝ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hsmall : τ ≤ η / 240)
    (hM : 0 ≤ M) (hgain : (32 + M) * τ ≤ 2 * η)
    (houter : τ ^ 2 * (45 / 8 + η) < 1 / 2)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hl₁ : -1 ≤ l₁) (hlr₁ : l₁ ≤ r₁) (hr₁ : r₁ ≤ 1)
    (hl₂ : -1 ≤ l₂) (hlr₂ : l₂ ≤ r₂) (hr₂ : r₂ ≤ 1)
    (hmesh₁ : r₁ - l₁ ≤ M * τ ^ 2) (hmesh₂ : r₂ - l₂ ≤ M * τ ^ 2)
    (hS0 : 0 ≤ S) (hT0 : 0 ≤ T)
    (hS : S = s - (τ * x) * ((l₁ + r₁) / 4))
    (hT : T = 1 - s + (τ * y) * ((l₂ + r₂) / 4))
    (hleft₁ : l₁ * S ≤ y - (τ * x) * ((1 + l₁ * r₁) / 4))
    (hright₁ : y - (τ * x) * ((1 + l₁ * r₁) / 4) ≤ r₁ * S)
    (hleft₂ : l₂ * T ≤ x + (τ * y) * ((1 + l₂ * r₂) / 4))
    (hright₂ : x + (τ * y) * ((1 + l₂ * r₂) / 4) ≤ r₂ * T) :
    (y - (τ * x) * ((1 + l₁ * r₁) / 4), S) ∈ domain τ η 1 ∨
      (x + (τ * y) * ((1 + l₂ * r₂) / 4), T) ∈ domain τ η 1 := by
  by_contra! hfail
  have hδ₁ : |τ * x| ≤ τ := by
    rw [abs_mul, abs_of_nonneg hτ.le]
    simpa using mul_le_mul_of_nonneg_left hx hτ.le
  have hδ₂ : |-(τ * y)| ≤ τ := by
    rw [abs_neg, abs_mul, abs_of_nonneg hτ.le]
    simpa using mul_le_mul_of_nonneg_left hy hτ.le
  have hfirst := selected_domain_gain hl₁ hlr₁ hr₁ hy hδ₁ hτ.le hτ1 hM hmesh₁
    hgain houter hS0 hS hleft₁ hright₁ hfail.1
  have hsecond := selected_domain_gain hl₂ hlr₂ hr₂ hx hδ₂ hτ.le hτ1 hM hmesh₂
    hgain houter hT0
    (show T = (1-s) - (-(τ*y)) * ((l₂+r₂)/4) by nlinarith only [hT])
    (by simpa only [neg_mul, sub_neg_eq_add] using hleft₂)
    (by simpa only [neg_mul, sub_neg_eq_add] using hright₂)
    (by simpa only [neg_mul, sub_neg_eq_add] using hfail.2)
  have hQ₁ : s ^ 2 - (τ * x) * y + (τ * x) ^ 2 / 4 =
      s ^ 2 - τ * x * y + τ ^ 2 * x ^ 2 / 4 := by ring
  have hQ₂ : (1 - s) ^ 2 - (-(τ * y)) * x + (-(τ * y)) ^ 2 / 4 =
      (1 - s) ^ 2 + τ * x * y + τ ^ 2 * y ^ 2 / 4 := by ring
  rw [hQ₁] at hfirst
  rw [hQ₂] at hsecond
  rcases discriminant_alternative hτ hτ1 hsmall hx hy hs0 hs1 with h | h
  · exact (not_lt_of_ge h) hfirst
  · exact (not_lt_of_ge h) hsecond

theorem uniform_selected_pair_domains {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      ∀ x y s l₁ r₁ l₂ r₂ S T : ℝ,
      |x| ≤ 1 → |y| ≤ 1 → 0 ≤ s → s ≤ 1 →
      -1 ≤ l₁ → l₁ ≤ r₁ → r₁ ≤ 1 → -1 ≤ l₂ → l₂ ≤ r₂ → r₂ ≤ 1 →
      r₁ - l₁ ≤ M * τ ^ 2 → r₂ - l₂ ≤ M * τ ^ 2 → 0 ≤ S → 0 ≤ T →
      S = s - (τ * x) * ((l₁ + r₁) / 4) →
      T = 1 - s + (τ * y) * ((l₂ + r₂) / 4) →
      l₁ * S ≤ y - (τ * x) * ((1 + l₁ * r₁) / 4) →
      y - (τ * x) * ((1 + l₁ * r₁) / 4) ≤ r₁ * S →
      l₂ * T ≤ x + (τ * y) * ((1 + l₂ * r₂) / 4) →
      x + (τ * y) * ((1 + l₂ * r₂) / 4) ≤ r₂ * T →
      (y - (τ * x) * ((1 + l₁ * r₁) / 4), S) ∈ domain τ η 1 ∨
        (x + (τ * y) * ((1 + l₂ * r₂) / 4), T) ∈ domain τ η 1 := by
  obtain ⟨δ, hδ, hδspec⟩ := smallness_radius hη hM
  refine ⟨min δ (η / 240), lt_min hδ (by positivity), ?_⟩
  intro τ hτ hτsmall x y s l₁ r₁ l₂ r₂ S T hx hy hs0 hs1 hl₁ hlr₁ hr₁
    hl₂ hlr₂ hr₂ hmesh₁ hmesh₂ hS0 hT0 hS hT hleft₁ hright₁ hleft₂ hright₂
  obtain ⟨hτ1, hgain, houter⟩ := hδspec τ hτ.le (hτsmall.trans (min_le_left _ _))
  exact selected_pair_domains hτ hτ1 (hτsmall.trans (min_le_right _ _)) hM hgain houter
    hx hy hs0 hs1 hl₁ hlr₁ hr₁ hl₂ hlr₂ hr₂ hmesh₁ hmesh₂ hS0 hT0 hS hT
    hleft₁ hright₁ hleft₂ hright₂

end AngularCartesianDirect

end OAI
