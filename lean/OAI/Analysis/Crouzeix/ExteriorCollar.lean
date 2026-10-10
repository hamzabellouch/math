import Mathlib
import OAI.Analysis.Crouzeix.ExteriorBoundaryChart

namespace OAI

/-! Exterior Collar. -/

noncomputable section

open Set Filter Metric Topology Function Complex

open scoped Classical

namespace CrouzeixHilbert.Conformal

def inversionChart (a : ℂ) : OpenPartialHomeomorph ℂ ℂ where
  toFun z := a + z⁻¹
  invFun z := (z - a)⁻¹
  source := {z | z ≠ 0}
  target := {z | z ≠ a}
  map_source' z hz := by
    change a + z⁻¹ ≠ a
    simpa only [ne_eq, add_eq_left, inv_eq_zero] using (show z ≠ 0 from hz)
  map_target' z hz := inv_ne_zero (sub_ne_zero.mpr hz)
  left_inv' z _ := by simp only [add_sub_cancel_left, inv_inv]
  right_inv' z _ := by simp only [inv_inv, add_sub_cancel]
  open_source := isClosed_singleton.isOpen_compl
  open_target := isClosed_singleton.isOpen_compl
  continuousOn_toFun z hz := (continuousAt_const.add (continuousAt_inv₀ hz)).continuousWithinAt
  continuousOn_invFun z hz := ((continuousAt_id.sub continuousAt_const).inv₀
    (sub_ne_zero.mpr hz)).continuousWithinAt

theorem mem_closure_invertedExterior {U : Set ℂ} (hU : IsOpen U)
    (hc : Convex ℝ U) (hne : U.Nonempty) (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    z ∈ closure (invertedExterior (closure U) a) ↔ a + z⁻¹ ∉ U := by
  have hi : (inversionChart a).IsImage (invertedExterior (closure U) a) (closure U)ᶜ := by
    intro w hw
    change a + w⁻¹ ∉ closure U ↔ w = 0 ∨ a + w⁻¹ ∉ closure U
    simp only [show w ≠ 0 from hw, false_or]
  have hreg : interior (closure U) = U :=
    (hc.interior_closure_eq_interior_of_nonempty_interior (hU.interior_eq.symm ▸ hne)).trans hU.interior_eq
  have he := (hi.closure hz).symm
  change (z ∈ closure (invertedExterior (closure U) a) ↔ a + z⁻¹ ∈ closure (closure U)ᶜ) at he
  simpa only [closure_compl, hreg, mem_compl_iff] using he

structure ExteriorCollar (U : Set ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  G : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ G {t | radius < ‖t‖}
  injective : InjOn G {t | radius < ‖t‖}
  outside : BijOn G {t | 1 < ‖t‖} (closure U)ᶜ
  boundary : BijOn G (sphere 0 1) (frontier U)
  inside : MapsTo G {t | radius < ‖t‖ ∧ ‖t‖ < 1} U
  leading : ℂ
  leading_ne_zero : leading ≠ 0
  regular : ℂ → ℂ
  regular_analytic : AnalyticOnNhd ℂ regular (ball 0 radius⁻¹)
  laurent : ∀ t, radius < ‖t‖ → G t = leading * t + regular t⁻¹

theorem reciprocal_simple_pole {ρ : ℝ} (hρ : 0 < ρ) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (ball 0 ρ)) (hi : InjOn h (ball 0 ρ)) (h0 : h 0 = 0)
    (a : ℂ) :
    ∃ (b : ℂ) (g : ℂ → ℂ), b ≠ 0 ∧ AnalyticOnNhd ℂ g (ball 0 ρ) ∧
      ∀ t : ℂ, ρ⁻¹ < ‖t‖ → a + (h t⁻¹)⁻¹ = b * t + g t⁻¹ := by
  let k := dslope h 0
  have hk : AnalyticOnNhd ℂ k (ball 0 ρ) :=
    ((differentiableOn_dslope (ball_mem_nhds 0 hρ)).mpr hh.differentiableOn).analyticOnNhd isOpen_ball
  have hkn : ∀ z ∈ ball 0 ρ, k z ≠ 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      simpa only [k, dslope_same] using
        deriv_ne_zero_of_injOn isOpen_ball hh.differentiableOn hi (mem_ball_self hρ)
    · have hn : h z ≠ 0 := fun he => hz0 (hi hz (mem_ball_self hρ) (he.trans h0.symm))
      simpa only [k, dslope_of_ne h hz0, slope_def_field, sub_zero, h0] using div_ne_zero hn hz0
  let l := fun z => (k z)⁻¹
  have hl : AnalyticOnNhd ℂ l (ball 0 ρ) := fun z hz => (hk z hz).inv (hkn z hz)
  let g := fun z => a + dslope l 0 z
  have hg : AnalyticOnNhd ℂ g (ball 0 ρ) := fun z hz =>
    analyticAt_const.add (((differentiableOn_dslope (ball_mem_nhds 0 hρ)).mpr hl.differentiableOn).analyticOnNhd isOpen_ball z hz)
  refine ⟨l 0, g, inv_ne_zero (hkn 0 (mem_ball_self hρ)), hg, ?_⟩
  intro t ht
  have ht0 : t ≠ 0 := norm_pos_iff.mp ((inv_pos.mpr hρ).trans ht)
  have hu0 := inv_ne_zero ht0
  have hhu : h t⁻¹ ≠ 0 := by
    have hu : t⁻¹ ∈ ball 0 ρ := mem_ball_zero_iff.mpr (by
      rw [norm_inv]; exact (inv_lt_comm₀ (norm_pos_iff.mpr ht0) hρ).mpr ht)
    exact fun he => hu0 (hi hu (mem_ball_self hρ) (he.trans h0.symm))
  simp only [g, k, l, dslope_of_ne h hu0, h0, sub_zero, slope_def_field,
    dslope_of_ne (fun z => (dslope h 0 z)⁻¹) hu0]
  field_simp
  ring

theorem exists_exteriorCollar {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : Convex ℝ U) {a : ℂ} (ha : a ∈ U)
    (hchart : ∀ p ∈ frontier U, Nonempty (BoundaryChart U p)) :
    Nonempty (ExteriorCollar U) := by
  obtain ⟨V, ρ, f, h, hV, hIV, hρ, hf, hh, hfi, hhi, hfb, hhb, hfc, hhc,
    hinv, hf0, hh0, hfront, hinvV, hρV⟩ := exists_inverted_exterior_collar hU hb hc ha hchart
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  let I := invertedExterior (closure U) a
  let G : ℂ → ℂ := fun t => a + (h t⁻¹)⁻¹
  have ht0 : ∀ t : ℂ, ρ⁻¹ < ‖t‖ → t ≠ 0 := fun t ht =>
    norm_pos_iff.mp ((inv_pos.mpr hρ0).trans ht)
  have hti : ∀ t : ℂ, ρ⁻¹ < ‖t‖ → t⁻¹ ∈ ball 0 ρ := by
    intro t ht
    rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr (ht0 t ht)) hρ0).mpr ht
  have hhn : ∀ z ∈ ball 0 ρ, z ≠ 0 → h z ≠ 0 :=
    fun z hz hz0 he => hz0 (hhi hz (mem_ball_self hρ0) (he.trans hh0.symm))
  have hhiC : InvOn h f (closure I) (closedBall 0 1) :=
    ⟨hinvV.1.mono hIV, hinvV.2.mono ((closedBall_subset_ball hρ).trans hρV)⟩
  have hr1 : ρ⁻¹ < 1 := (inv_lt_one₀ hρ0).mpr hρ
  have hGinj : InjOn G {t | ρ⁻¹ < ‖t‖} := by
    intro t ht s hs he
    exact inv_injective (hhi (hti t ht) (hti s hs) (inv_injective (add_left_cancel he)))
  have hGe : ∀ t : ℂ, 1 ≤ ‖t‖ → t⁻¹ ∈ closedBall 0 1 := by
    intro t ht
    rw [mem_closedBall_zero_iff, norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le ht)).mpr ht
  have hGo : ∀ t : ℂ, 1 < ‖t‖ → t⁻¹ ∈ ball 0 1 := by
    intro t ht
    rw [mem_ball_zero_iff, norm_inv]
    exact (inv_lt_one₀ (zero_lt_one.trans ht)).mpr ht
  have hGb : BijOn G {t | 1 < ‖t‖} (closure U)ᶜ := by
    refine ⟨?_, hGinj.mono (fun t ht => hr1.trans ht), ?_⟩
    · intro t ht
      exact (hhb.mapsTo (hGo t ht)).resolve_left (hhn _ (hti t (hr1.trans ht)) (inv_ne_zero (ht0 t (hr1.trans ht))))
    · intro z hz
      have hza : z - a ≠ 0 := fun he => hz (sub_eq_zero.mp he ▸ subset_closure ha)
      have hzi : (z - a)⁻¹ ∈ I := Or.inr (by simpa only [inv_inv, add_sub_cancel, mem_compl_iff] using hz)
      let v := f (z - a)⁻¹
      have hv : v ∈ ball 0 1 := hfb.mapsTo hzi
      have hv0 : v ≠ 0 := fun he => inv_ne_zero hza
        (hfb.injOn hzi (zero_mem_invertedExterior _ _) (he.trans hf0.symm))
      refine ⟨v⁻¹, ?_, ?_⟩
      · change 1 < ‖v⁻¹‖
        rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr hv0)]
        exact mem_ball_zero_iff.mp hv
      · simp only [G, inv_inv, v, hinv.1 hzi, add_sub_cancel]
  have hGf : BijOn G (sphere 0 1) (frontier U) := by
    refine ⟨?_, hGinj.mono (fun t ht => by change ρ⁻¹ < ‖t‖; rwa [mem_sphere_zero_iff_norm.mp ht]), ?_⟩
    · intro t ht
      have htn : ‖t‖ = 1 := mem_sphere_zero_iff_norm.mp ht
      have htS : ρ⁻¹ < ‖t‖ := htn ▸ hr1
      have htvn : ‖t⁻¹‖ = 1 := by rw [norm_inv, htn, inv_one]
      have hin : h t⁻¹ ∈ frontier I := by
        refine ⟨hhc.mapsTo (hGe t htn.ge), ?_⟩
        rw [(isOpen_invertedExterior hb.isCompact_closure a).interior_eq]
        intro he
        have heq := hhiC.2 (hGe t htn.ge)
        have hsmall := mem_ball_zero_iff.mp (hfb.mapsTo he)
        rw [heq, htvn] at hsmall
        exact (lt_irrefl 1 hsmall)
      exact (frontier_invertedExterior hU hb a hin).2
    · intro z hz
      have hza : z - a ≠ 0 := fun he => hz.2 (by rw [hU.interior_eq]; exact sub_eq_zero.mp he ▸ ha)
      let v := (z - a)⁻¹
      have hv0 : v ≠ 0 := inv_ne_zero hza
      have hvC : v ∈ closure I := (mem_closure_invertedExterior hU hc ⟨a, ha⟩ a hv0).mpr (by
        simpa only [v, inv_inv, add_sub_cancel, hU.interior_eq] using hz.2)
      have hvn : v ∉ I := by
        intro he
        have := he.resolve_left hv0
        exact this (by simpa only [v, inv_inv, add_sub_cancel] using hz.1)
      have hvF : v ∈ frontier I := ⟨hvC, fun he => hvn (interior_subset he)⟩
      have hfv : ‖f v‖ = 1 := hfront _ hvF
      refine ⟨(f v)⁻¹, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_inv, hfv, inv_one]
      · change a + (h ((f v)⁻¹)⁻¹)⁻¹ = z
        rw [inv_inv, hhiC.1 hvC]
        simp only [v, inv_inv, add_sub_cancel]
  have hGin : MapsTo G {t | ρ⁻¹ < ‖t‖ ∧ ‖t‖ < 1} U := by
    intro t ht
    by_contra hn
    have hvC : h t⁻¹ ∈ closure I :=
      (mem_closure_invertedExterior hU hc ⟨a, ha⟩ a
        (hhn _ (hti t ht.1) (inv_ne_zero (ht0 t ht.1)))).mpr hn
    obtain ⟨v, hv, he⟩ := hhc.surjOn hvC
    have hvt : v = t⁻¹ := hhi ((closedBall_subset_ball hρ) hv) (hti t ht.1) he
    have hle : ‖t‖⁻¹ ≤ 1 := by simpa only [hvt, norm_inv, mem_closedBall_zero_iff] using hv
    exact (not_le_of_gt ht.2) ((inv_le_one₀ (norm_pos_iff.mpr (ht0 t ht.1))).mp hle)
  have hGa : AnalyticOnNhd ℂ G {t | ρ⁻¹ < ‖t‖} := by
    intro t ht
    exact analyticAt_const.add (((hh _ (hti t ht)).comp
      (analyticAt_id.inv (ht0 t ht))).inv (hhn _ (hti t ht) (inv_ne_zero (ht0 t ht))))
  obtain ⟨b, g, hbn, hga, hLaur⟩ := reciprocal_simple_pole hρ0 hh hhi hh0 a
  exact ⟨⟨ρ⁻¹, inv_pos.mpr hρ0, hr1, G, hGa, hGinj, hGb, hGf, hGin,
    b, hbn, g, by simpa only [inv_inv] using hga, hLaur⟩⟩

end CrouzeixHilbert.Conformal

end

end OAI
