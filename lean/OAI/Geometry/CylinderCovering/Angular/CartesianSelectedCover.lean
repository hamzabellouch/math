import OAI.Geometry.CylinderCovering.Angular.CartesianDirect
import OAI.Geometry.CylinderCovering.Angular.CartesianObstruction

namespace OAI

namespace AngularCartesianDirect
open CylinderCovering.CartesianCaps

theorem selected_pair_cover {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
      ∀ x y s l r l' r' S T : ℝ,
      |x| ≤ 1 → |y| ≤ 1 → 0 ≤ s → s ≤ 1 →
      -1 ≤ l → l ≤ r → r ≤ 1 → -1 ≤ l' → l' ≤ r' → r' ≤ 1 →
      r-l ≤ M*τ^2 → r'-l' ≤ M*τ^2 →
      0 ≤ S → 0 ≤ T → S = s-τ*x*((l+r)/4) → T = 1-s+τ*y*((l'+r')/4) →
      l*S ≤ y-τ*x*((1+l*r)/4) → y-τ*x*((1+l*r)/4) ≤ r*S →
      l'*T ≤ x+τ*y*((1+l'*r')/4) → x+τ*y*((1+l'*r')/4) ≤ r'*T →
      (y-τ*x*((1+l*r)/4), S) ∈ domain τ η 1 ∨
        (x+τ*y*((1+l'*r')/4), T) ∈ domain τ η 1 := by
  obtain ⟨a, ha, hsmall⟩ := smallness_radius hη hM
  refine ⟨min a (η/240), lt_min ha (by positivity), ?_⟩
  intro τ hτ hτle x y s l r l' r' S T hx hy hs0 hs1 hl hlr hr hl' hlr' hr'
    hmesh hmesh' hS0 hT0 hS hT hleft hright hleft' hright'
  obtain ⟨hτ1, hmarg, houter⟩ := hsmall τ hτ.le (hτle.trans (min_le_left _ _))
  have hfinal : τ ≤ η/240 := hτle.trans (min_le_right _ _)
  by_contra! hfail
  have hδ : |τ*x| ≤ τ := by
    rw [abs_mul, abs_of_pos hτ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hx hτ.le
  have hδ' : |-(τ*y)| ≤ τ := by
    rw [abs_neg, abs_mul, abs_of_pos hτ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hy hτ.le
  have hgain := selected_domain_gain hl hlr hr hy hδ hτ.le hτ1 hM hmesh hmarg
    houter hS0 hS hleft hright hfail.1
  have hT' : T = (1-s)-(-(τ*y))*((l'+r')/4) := by rw [hT]; ring
  have hleft'' : l'*T ≤ x-(-(τ*y))*((1+l'*r')/4) := by
    simpa only [neg_mul, sub_neg_eq_add] using hleft'
  have hright'' : x-(-(τ*y))*((1+l'*r')/4) ≤ r'*T := by
    simpa only [neg_mul, sub_neg_eq_add] using hright'
  have hfail' : (x-(-(τ*y))*((1+l'*r')/4), T) ∉ domain τ η 1 := by
    simpa only [neg_mul, sub_neg_eq_add] using hfail.2
  have hgain' := selected_domain_gain hl' hlr' hr' hx hδ' hτ.le hτ1 hM hmesh'
    hmarg houter hT0 hT' hleft'' hright'' hfail'
  have hQ : s^2-(τ*x)*y+(τ*x)^2/4 = s^2-τ*x*y+τ^2*x^2/4 := by ring
  have hQ' : (1-s)^2-(-(τ*y))*x+(-(τ*y))^2/4 =
      (1-s)^2+τ*x*y+τ^2*y^2/4 := by ring
  rw [hQ] at hgain
  rw [hQ'] at hgain'
  rcases discriminant_alternative hτ hτ1 hfinal hx hy hs0 hs1 with hfirst | hsecond
  · exact (not_lt_of_ge hfirst) hgain
  · exact (not_lt_of_ge hsecond) hgain'

end AngularCartesianDirect

end OAI
