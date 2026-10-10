import OAI.Probability.SLE.Geometry.NormalizedAccessGuide
import OAI.Probability.SLE.Geometry.PublishedCrosscutStraightening

namespace OAI

/-! The complete physical access guide maps to a proper half-plane
crosscut based at the actual driving prime end. Properness at infinity
is proved from the hydrodynamic normalization in the capacity witness. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem IsCapacityTwoWitness.centered_chart_escapes
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0)
    (α : ℝ≥0 → ℂ) (hαD : ∀ t : ℝ≥0, 0 < t → α t ∈ survivingDomain γ T)
    (hescape : Tendsto α atTop (cocompact ℂ)) :
    Tendsto (fun t => G T (α t) - (U T : ℂ)) atTop (cocompact ℂ) := by
  have hnorm := hw
  rcases hnorm with ⟨_, _, _, _, _, _, _, _, _, _, _, hnorm, _⟩
  have hD : ∀ᶠ t in atTop, α t ∈ survivingDomain γ T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    exact hαD t ht
  have hmap : Tendsto α atTop (cocompact ℂ ⊓ 𝓟 (survivingDomain γ T)) :=
    by simpa only [inf_idem] using hescape.inf (tendsto_principal.mpr hD)
  have hproduct := (hnorm T).comp hmap
  have hinv : Tendsto (fun t => (α t)⁻¹) atTop (𝓝 (0 : ℂ)) :=
    tendsto_inv₀_cobounded.comp (hescape.mono_right cobounded_eq_cocompact.ge)
  have hprod0 := hproduct.mul hinv
  have hαnorm : Tendsto (fun t => ‖α t‖) atTop atTop :=
    tendsto_norm_cocompact_atTop.comp hescape
  have hne : ∀ᶠ t in atTop, α t ≠ 0 := by
    filter_upwards [hαnorm.eventually_gt_atTop 0] with t ht
    exact norm_pos_iff.mp ht
  have hdiff : Tendsto (fun t => G T (α t) - α t) atTop (𝓝 (0 : ℂ)) := by
    have he : (fun t => (α t * (G T (α t) - α t)) * (α t)⁻¹) =ᶠ[atTop]
        (fun t => G T (α t) - α t) := by
      filter_upwards [hne] with t ht
      field_simp
    simpa only [mul_zero] using hprod0.congr' he
  apply tendsto_cocompact_of_tendsto_dist_comp_atTop 0
  simp only [dist_zero_right]
  apply Filter.tendsto_atTop.mpr
  intro R
  have hsmall : ∀ᶠ t in atTop, ‖G T (α t) - α t‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hdiff.eventually (ball_mem_nhds 0 zero_lt_one)
  filter_upwards [hαnorm.eventually_ge_atTop (R + |U T| + 1), hsmall] with t ht hs
  have htri : ‖α t‖ ≤ ‖α t - (G T (α t) - (U T : ℂ))‖ +
      ‖G T (α t) - (U T : ℂ)‖ := by
    simpa only [add_comm] using norm_le_insert' (α t) (G T (α t) - (U T : ℂ))
  have he : α t - (G T (α t) - (U T : ℂ)) =
      -(G T (α t) - α t) + (U T : ℂ) := by ring
  have hb : ‖α t - (G T (α t) - (U T : ℂ))‖ ≤
      ‖G T (α t) - α t‖ + |U T| := by
    rw [he]
    simpa only [norm_neg, Complex.norm_real, Real.norm_eq_abs] using
      norm_add_le (-(G T (α t) - α t)) (U T : ℂ)
  linarith

/-- The continuous complete parameter guide has the exact capacity-map
formula at every positive time, including its asymptotic endpoint. -/
theorem actual_complete_access_guide
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (hT : 0 < T)
    (hfresh : ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s)
    (α : ℝ≥0 → ℂ) (hα : Continuous α) (hiα : Function.Injective α)
    (hα0 : α 0 = γ T) (hαD : ∀ t : ℝ≥0, 0 < t → α t ∈ survivingDomain γ T)
    (hescape : Tendsto α atTop (cocompact ℂ)) :
    ∃ β : ℝ≥0 → ℂ, Continuous β ∧ Function.Injective β ∧ β 0 = 0 ∧
      (∀ t : ℝ≥0, 0 < t → β t ∈ upperHalfPlane) ∧
      Tendsto β atTop (cocompact ℂ) ∧
      ∀ t : ℝ≥0, 0 < t → β t = G T (α t) - (U T : ℂ) := by
  let D := survivingDomain γ T
  have htip : γ T ∉ D := fun hh => hh.1.2 ⟨T, ⟨bot_le, le_rfl⟩, rfl⟩
  let gb := Function.update (G T) (γ T) (U T : ℂ)
  have hs : insert (γ T) D \ {γ T} = D := by
    ext z
    simp only [Set.mem_sdiff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | hz, hn⟩
      · exact False.elim (hn rfl)
      · exact hz
    · intro hz
      exact ⟨Or.inr hz, fun he => htip (he ▸ hz)⟩
  have hgb : ContinuousOn gb (insert (γ T) D) := by
    rw [continuousOn_update_iff, hs]
    exact ⟨(hw.2.2.2.1 T).continuousOn,
      fun _ => hw.fresh_tip_chart_tendsto hU hT hfresh⟩
  have hαS : MapsTo α univ (insert (γ T) D) := by
    intro t _
    by_cases ht : t = 0
    · simpa only [ht, hα0] using mem_insert (γ T) D
    · exact mem_insert_of_mem _ (hαD t (pos_iff_ne_zero.mpr ht))
  let β : ℝ≥0 → ℂ := fun t => gb (α t) - (U T : ℂ)
  have hβc : Continuous β :=
    (hgb.comp_continuous hα (fun t => hαS (mem_univ t))).sub continuous_const
  have hβ0 : β 0 = 0 := by simp [β, gb, hα0]
  have hβeq (t : ℝ≥0) (ht : 0 < t) : β t = G T (α t) - (U T : ℂ) := by
    have hn : α t ≠ γ T := fun he => htip (he ▸ hαD t ht)
    exact congrArg (fun z : ℂ => z - (U T : ℂ)) (Function.update_of_ne hn _ _)
  have hβH (t : ℝ≥0) (ht : 0 < t) : β t ∈ upperHalfPlane := by
    rw [hβeq t ht]
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im, sub_zero]
      using hw.imag_positive T (α t) (hαD t ht)
  have hβi : Function.Injective β := by
    intro s t he
    by_cases hs0 : s = 0
    · have ht0 : t = 0 := by
        by_contra ht0
        have hh : 0 < (β t).im := hβH t (pos_iff_ne_zero.mpr ht0)
        rw [← he, hs0, hβ0, Complex.zero_im] at hh
        exact (lt_irrefl 0) hh
      exact hs0.trans ht0.symm
    · by_cases ht0 : t = 0
      · have hh : 0 < (β s).im := hβH s (pos_iff_ne_zero.mpr hs0)
        rw [he, ht0, hβ0, Complex.zero_im] at hh
        exact False.elim ((lt_irrefl 0) hh)
      · apply hiα
        rw [hβeq s (pos_iff_ne_zero.mpr hs0), hβeq t (pos_iff_ne_zero.mpr ht0)] at he
        have hg : G T (α s) = G T (α t) := sub_left_inj.mp he
        calc
          α s = F T (G T (α s)) :=
            (hw.2.2.2.2.2.2.2.1 T _ (hαD s (pos_iff_ne_zero.mpr hs0))).symm
          _ = F T (G T (α t)) := congrArg (F T) hg
          _ = α t := hw.2.2.2.2.2.2.2.1 T _ (hαD t (pos_iff_ne_zero.mpr ht0))
  have hβescape : Tendsto β atTop (cocompact ℂ) := by
    apply (hw.centered_chart_escapes T α hαD hescape).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    exact (hβeq t ht).symm
  exact ⟨β, hβc, hβi, hβ0, hβH, hβescape, hβeq⟩

end SLEExactGauge

end

end OAI
