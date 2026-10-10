import OAI.InformationTheory.BooleanNoise.LRegularity

namespace OAI

noncomputable section

open Set

namespace LeanBlast.CourtadeKumar

theorem L_eq_rGap_max {x : ℝ} (hx : 0 < x) :
    L x = rGap (max (ell - x) 0) := by
  by_cases hxl : x < ell
  · rw [L_eq_rGap ⟨hx, hxl⟩, max_eq_left (sub_nonneg.mpr hxl.le)]
  · rw [L_eq_zero_of_ell_le (le_of_not_gt hxl),
      max_eq_right (sub_nonpos.mpr (le_of_not_gt hxl)), rGap_zero]

theorem positivePart_ell_sub_mem {x : ℝ} (hx : 0 < x) :
    max (ell - x) 0 ∈ Ico 0 ell := by
  exact ⟨le_max_right _ _, max_lt (by linarith) ell_pos⟩

theorem L_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ L x := by
  rw [L_eq_rGap_max hx]
  exact rGap_nonneg (positivePart_ell_sub_mem hx).1 (positivePart_ell_sub_mem hx).2

theorem antitoneOn_L : AntitoneOn L (Ioi 0) := by
  intro x hx y hy hxy
  rw [L_eq_rGap_max hx, L_eq_rGap_max hy]
  exact monotoneOn_rGap (positivePart_ell_sub_mem hy) (positivePart_ell_sub_mem hx)
    (max_le_max (sub_le_sub_left hxy ell) le_rfl)

theorem convexOn_L : ConvexOn ℝ (Ioi 0) L := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : 0 < a * x + b * y := by
    simpa only [smul_eq_mul, mem_Ioi] using (convex_Ioi (0 : ℝ)) hx hy ha hb hab
  have hsum : a * max (ell - x) 0 + b * max (ell - y) 0 ∈ Ico 0 ell := by
    simpa only [smul_eq_mul] using
      (convex_Ico (0 : ℝ) ell) (positivePart_ell_sub_mem hx)
        (positivePart_ell_sub_mem hy) ha hb hab
  have hmax : max (ell - (a * x + b * y)) 0 ≤
      a * max (ell - x) 0 + b * max (ell - y) 0 := by
    apply max_le
    · calc
        ell - (a * x + b * y) = a * (ell - x) + b * (ell - y) := by
          nlinarith [congrArg (fun t : ℝ => t * ell) hab]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _))
        (mul_nonneg hb (le_max_right _ _))
  simp only [smul_eq_mul]
  rw [L_eq_rGap_max hz, L_eq_rGap_max hx, L_eq_rGap_max hy]
  exact (monotoneOn_rGap (positivePart_ell_sub_mem hz) hsum hmax).trans
    (convexOn_rGap.2 (positivePart_ell_sub_mem hx) (positivePart_ell_sub_mem hy)
      ha hb hab)

theorem L_tangent_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    L x + LDeriv x * (y - x) ≤ L y := by
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := convexOn_L.le_slope_of_hasDerivAt hx hy hxy (hasDerivAt_L hx)
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
    linarith
  · simp
  · have hs := convexOn_L.slope_le_of_hasDerivAt hy hx hyx (hasDerivAt_L hx)
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr hyx)).mp hs
    nlinarith

theorem L_support : ∀ x, 0 < x → ∀ y, 0 < y →
    L x + LDeriv x * (y - x) ≤ L y :=
  fun _ hx _ hy => L_tangent_le hx hy

end LeanBlast.CourtadeKumar

end

end OAI
