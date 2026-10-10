import OAI.InformationTheory.BooleanNoise.InverseRegularity
import OAI.InformationTheory.BooleanNoise.CurvatureBounds

namespace OAI

noncomputable section

open Set Filter
open scoped Topology

namespace LeanBlast.CourtadeKumar

def LSecondDeriv (x : ℝ) : ℝ :=
  if x < ell then rSecondDeriv (ell - x) else 0

theorem LDeriv_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : LDeriv x = 0 := by
  simp [LDeriv, not_lt.mpr hx]

theorem LSecondDeriv_eq_zero_of_ell_le {x : ℝ} (hx : ell ≤ x) : LSecondDeriv x = 0 := by
  simp [LSecondDeriv, not_lt.mpr hx]

private theorem L_eq_rGap_on_left {x : ℝ} (hx : x ∈ Ioc 0 ell) :
    L x = rGap (ell - x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact L_eq_rGap ⟨hx.1, hlt⟩
  · simp [L]

private theorem LDeriv_eq_formula_on_left {x : ℝ} (hx : x ∈ Ioc 0 ell) :
    LDeriv x = 2 - rDeriv (ell - x) := by
  rcases hx.2.lt_or_eq with hlt | rfl
  · exact ite_eq_left ⟨hx.1, hlt⟩
  · simp [LDeriv]

private theorem L_join_neighborhood : Ioc (0 : ℝ) ell ∪ Ici ell ∈ 𝓝 ell := by
  apply mem_of_superset (Ioi_mem_nhds ell_pos)
  intro x hx
  rcases le_total x ell with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr h

theorem hasDerivAt_L_of_gt {x : ℝ} (hx : ell < x) :
    HasDerivAt L (LDeriv x) x := by
  have he : L =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact L_eq_zero_of_ell_le (le_of_lt hy)
  rw [LDeriv_eq_zero_of_ell_le hx.le]
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he

theorem hasDerivAt_LDeriv_of_gt {x : ℝ} (hx : ell < x) :
    HasDerivAt LDeriv 0 x := by
  have he : LDeriv =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact LDeriv_eq_zero_of_ell_le (le_of_lt hy)
  exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he

theorem hasDerivAt_LDeriv {x : ℝ} (hx : 0 < x) (hne : x ≠ ell) :
    HasDerivAt LDeriv (LSecondDeriv x) x := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · simpa only [LSecondDeriv, ite_eq_left hlt] using hasDerivAt_LDeriv_of_lt ⟨hx, hlt⟩
  · rw [LSecondDeriv_eq_zero_of_ell_le hgt.le]
    exact hasDerivAt_LDeriv_of_gt hgt

theorem hasDerivAt_L_at_ell : HasDerivAt L (LDeriv ell) ell := by
  have hleft0 : HasDerivWithinAt (fun x : ℝ => rGap (ell - x)) 0 (Ioc 0 ell) ell := by
    convert! hasDerivWithinAt_rGap_zero.comp_of_eq ell
      ((hasDerivAt_id ell).const_sub ell).hasDerivWithinAt
      (show MapsTo (fun x : ℝ => ell - x) (Ioc 0 ell) (Ici 0) from
        fun x hx => sub_nonneg.mpr hx.2) (by simp) using 1
    simp
  have hleft : HasDerivWithinAt L 0 (Ioc 0 ell) ell :=
    hleft0.congr (fun _ hx => L_eq_rGap_on_left hx) (by simp [L])
  have hright : HasDerivWithinAt L 0 (Ici ell) ell :=
    (hasDerivAt_const ell (0 : ℝ)).hasDerivWithinAt.congr
      (fun _ hx => L_eq_zero_of_ell_le hx) (L_eq_zero_of_ell_le le_rfl)
  simpa only [LDeriv_eq_zero_of_ell_le (le_refl ell)] using
    (hleft.union hright).hasDerivAt L_join_neighborhood

theorem hasDerivAt_L {x : ℝ} (hx : 0 < x) : HasDerivAt L (LDeriv x) x := by
  rcases lt_trichotomy x ell with hlt | rfl | hgt
  · exact hasDerivAt_L_of_lt ⟨hx, hlt⟩
  · exact hasDerivAt_L_at_ell
  · exact hasDerivAt_L_of_gt hgt

theorem continuousAt_LDeriv_at_ell : ContinuousAt LDeriv ell := by
  have hr : ContinuousWithinAt rDeriv (Ico 0 ell) 0 :=
    continuousOn_rDeriv 0 ⟨le_rfl, ell_pos⟩
  have hcomp : ContinuousWithinAt (fun x : ℝ => rDeriv (ell - x)) (Ioc 0 ell) ell := by
    exact hr.comp_of_eq
      ((continuous_const.sub continuous_id).continuousWithinAt :
        ContinuousWithinAt (fun x : ℝ => ell - x) (Ioc 0 ell) ell)
      (show MapsTo (fun x : ℝ => ell - x) (Ioc 0 ell) (Ico 0 ell) from
        fun x hx => ⟨sub_nonneg.mpr hx.2, by linarith [hx.1]⟩) (by simp)
  have hleft : ContinuousWithinAt LDeriv (Ioc 0 ell) ell :=
    (continuousWithinAt_const.sub hcomp).congr
      (fun _ hx => LDeriv_eq_formula_on_left hx) (by simp [LDeriv])
  have hright : ContinuousWithinAt LDeriv (Ici ell) ell :=
    continuousWithinAt_const.congr (fun _ hx => LDeriv_eq_zero_of_ell_le hx)
      (LDeriv_eq_zero_of_ell_le le_rfl)
  exact (hleft.union hright).continuousAt L_join_neighborhood

theorem continuousOn_LDeriv : ContinuousOn LDeriv (Ioi 0) := by
  intro x hx
  by_cases hxe : x = ell
  · subst x
    exact continuousAt_LDeriv_at_ell.continuousWithinAt
  · exact (hasDerivAt_LDeriv hx hxe).continuousAt.continuousWithinAt

theorem continuousOn_L : ContinuousOn L (Ioi 0) :=
  fun _ hx => (hasDerivAt_L hx).continuousAt.continuousWithinAt

theorem LSecondDeriv_bound {x : ℝ} (hx : 0 < x) :
    x ^ 2 * LSecondDeriv x ≤ 2 / 3 := by
  by_cases h : x < ell
  · simpa only [LSecondDeriv, ite_eq_left h] using L_curvature_bound ⟨hx, h⟩
  · rw [LSecondDeriv_eq_zero_of_ell_le (le_of_not_gt h)]
    norm_num

end LeanBlast.CourtadeKumar

end

end OAI
