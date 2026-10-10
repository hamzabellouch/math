import Mathlib
import OAI.Analysis.Crouzeix.Convexity

namespace OAI

/-! Convex Neighborhood. -/

noncomputable section

open Set Metric

open scoped Convex InnerProductSpace

namespace CrouzeixHilbert

theorem convex_outward_not_mem {K : Set ℂ} (hK : Convex ℝ K)
    {a x : ℂ} (ha : a ∈ K) (hx : x ∉ K) {t : ℝ} (ht : 1 ≤ t) :
    a + t • (x - a) ∉ K := by
  intro hy
  have htp : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hz := hK.add_smul_sub_mem ha hy
    (show t⁻¹ ∈ Icc (0 : ℝ) 1 from
      ⟨inv_nonneg.mpr htp.le, inv_le_one_of_one_le₀ ht⟩)
  simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ htp.ne',
    one_smul, add_sub_cancel] at hz
  exact hx hz

theorem segment_outward_subset_compl {K : Set ℂ} (hK : Convex ℝ K)
    {a x : ℂ} (ha : a ∈ K) (hx : x ∉ K) {r : ℝ} (hr : 1 ≤ r) :
    [x -[ℝ] (a + r • (x - a))] ⊆ Kᶜ := by
  rw [segment_eq_image']
  rintro z ⟨t, ht, rfl⟩
  have he : x + t • (a + r • (x - a) - x) =
      a + (1 + t * (r - 1)) • (x - a) := by module
  dsimp only
  rw [he]
  exact convex_outward_not_mem hK ha hx (by nlinarith [ht.1])

theorem isPathConnected_compl_of_bounded_convex {K : Set ℂ}
    (hK : Bornology.IsBounded K) (hc : Convex ℝ K) : IsPathConnected Kᶜ := by
  rcases K.eq_empty_or_nonempty with h0 | ⟨a, ha⟩
  · rw [h0, compl_empty]
    exact convex_univ.isPathConnected ⟨0, mem_univ _⟩
  have hrank : 1 < Module.rank ℝ ℂ := by simp
  have hn : Kᶜ.Nonempty := by
    obtain ⟨R, hR, hb⟩ := hK.subset_ball_lt 0 a
    obtain ⟨z, hz⟩ := (isPathConnected_sphere hrank a hR.le).nonempty
    refine ⟨z, ?_⟩
    intro hzK
    have := mem_ball.mp (hb hzK)
    rw [mem_sphere.mp hz] at this
    exact lt_irrefl _ this
  apply isPathConnected_iff.mpr
  refine ⟨hn, ?_⟩
  intro x hx y hy
  obtain ⟨R, hR, hb⟩ := hK.subset_ball_lt (max (dist x a) (dist y a)) a
  have hRx : dist x a < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hRy : dist y a < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRp : 0 < R := lt_of_le_of_lt dist_nonneg hRx
  have hsphere : sphere a R ⊆ Kᶜ := by
    intro z hz hzK
    have hlt := mem_ball.mp (hb hzK)
    rw [mem_sphere.mp hz] at hlt
    exact lt_irrefl _ hlt
  have hradial (v : ℂ) (hv : v ∈ Kᶜ) (hRv : dist v a < R) :
      ∃ q ∈ sphere a R, JoinedIn Kᶜ v q := by
    have hvne : v - a ≠ 0 := by
      intro he
      exact hv (sub_eq_zero.mp he ▸ ha)
    have hnv : 0 < ‖v - a‖ := norm_pos_iff.mpr hvne
    have hr : 1 ≤ R / ‖v - a‖ := by
      apply (le_div_iff₀ hnv).mpr
      simpa only [one_mul, dist_eq_norm] using hRv.le
    refine ⟨a + (R / ‖v - a‖) • (v - a), ?_, ?_⟩
    · rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hRp.le hnv.le), div_mul_cancel₀ _ hnv.ne']
    · exact JoinedIn.of_segment_subset (segment_outward_subset_compl hc ha hv hr)
  obtain ⟨qx, hqx, jx⟩ := hradial x hx hRx
  obtain ⟨qy, hqy, jy⟩ := hradial y hy hRy
  exact jx.trans (((isPathConnected_sphere hrank a hRp.le).joinedIn qx hqx qy hqy).mono
    hsphere |>.trans jy.symm)

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_compact_convex_neighborhood (A : Operator H) {U : Set ℂ}
    (hU : IsOpen U) (hKU : numericalClosure A ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧
      IsCompact (cthickening ε (numericalClosure A)) ∧
      Convex ℝ (cthickening ε (numericalClosure A)) ∧
      numericalClosure A ⊆ interior (cthickening ε (numericalClosure A)) ∧
      cthickening ε (numericalClosure A) ⊆ U ∧
      IsConnected (cthickening ε (numericalClosure A))ᶜ := by
  obtain ⟨ε, hε, hεU⟩ := (isCompact_numericalClosure A).exists_cthickening_subset_open hU hKU
  have hcmp : IsCompact (cthickening ε (numericalClosure A)) :=
    (isCompact_numericalClosure A).cthickening
  have hc : Convex ℝ (cthickening ε (numericalClosure A)) :=
    (convex_numericalRange A).closure.cthickening ε
  exact ⟨ε, hε, hcmp, hc,
    (self_subset_thickening hε _).trans (thickening_subset_interior_cthickening _ _), hεU,
    (isPathConnected_compl_of_bounded_convex hcmp.isBounded hc).isConnected⟩

end CrouzeixHilbert

end

end OAI
