import OAI.Geometry.RCD.Heat.TwoRateEvolution

namespace OAI

/-! # Two evolution inequalities with independent positive time speeds -/

open Set Filter MeasureTheory
open scoped Topology
namespace RegularPointCoordinates

theorem two_rate_evi_rescaled {D G H : ℝ → ℝ → ℝ} {α β t : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t)
    (hG : ∀ a b : ℝ, 0 < a → 0 < b → ContinuousAt (Function.uncurry G) (a,b))
    (hH : ∀ a b : ℝ, 0 < a → 0 < b → ContinuousAt (Function.uncurry H) (a,b))
    (hI : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D b s-D a s)/2 ≤ ∫q in a..b, G q s)
    (hJ : ∀ a b s : ℝ, 0 < a → a ≤ b → 0 < s →
      (D s b-D s a)/2 ≤ ∫q in a..b, H s q) :
    ∀ r, 2*(α*G (α*t) (β*t)+β*H (α*t) (β*t)) < r →
      ∃ᶠ z in 𝓝[>] t, slope (fun q => D (α*q) (β*q)) t z < r := by
  apply two_rate_evi_frequent_slope (D := fun a b => D (α*a) (β*b))
    (G := fun a b => α*G (α*a) (β*b)) (H := fun a b => β*H (α*a) (β*b)) ht
  · intro a b ha hb
    exact continuousAt_const.mul ((hG _ _ (mul_pos hα ha) (mul_pos hβ hb)).comp (x := (a,b))
      (f := fun z : ℝ × ℝ => (α*z.1,β*z.2)) (by fun_prop))
  · intro a b ha hb
    exact continuousAt_const.mul ((hH _ _ (mul_pos hα ha) (mul_pos hβ hb)).comp (x := (a,b))
      (f := fun z : ℝ × ℝ => (α*z.1,β*z.2)) (by fun_prop))
  · intro a b s ha hab hs
    have hh := hI (α*a) (α*b) (β*s) (mul_pos hα ha)
      (mul_le_mul_of_nonneg_left hab hα.le) (mul_pos hβ hs)
    rwa [← intervalIntegral.smul_integral_comp_mul_left (fun q => G q (β*s)) α,
      smul_eq_mul, ← intervalIntegral.integral_const_mul] at hh
  · intro a b s ha hab hs
    have hh := hJ (β*a) (β*b) (α*s) (mul_pos hβ ha)
      (mul_le_mul_of_nonneg_left hab hβ.le) (mul_pos hα hs)
    rwa [← intervalIntegral.smul_integral_comp_mul_left (fun q => H (α*s) q) β,
      smul_eq_mul, ← intervalIntegral.integral_const_mul] at hh

theorem evolution_gronwall {D F : ℝ → ℝ} {a b k e : ℝ}
    (hab : a ≤ b) (hD : ContinuousOn D (Icc a b))
    (hs : ∀ t ∈ Ico a b, ∀ r, F t < r → ∃ᶠ z in 𝓝[>] t, slope D t z < r)
    (hbound : ∀ t ∈ Ico a b, F t ≤ k*D t+e) :
    D b ≤ gronwallBound (D a) k e (b-a) := by
  have hh := le_gronwallBound_of_liminf_deriv_right_le (f' := F) hD
    (by
      intro t ht r hr
      simpa only [slope_def_field,div_eq_mul_inv,mul_comm] using hs t ht r hr)
    le_rfl hbound b ⟨hab,le_rfl⟩
  exact hh

end RegularPointCoordinates

end OAI
