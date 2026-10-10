import OAI.Probability.SLE.Gauge.RibbonFrontFreshness
import OAI.Probability.SLE.Geometry.PublishedBoundaryExtension

namespace OAI

/-! Continuous normalized parameter guides from actual fresh Loewner tips.
The boundary value, inverse identity, simplicity and unit-waypoint
normalization are derived, rather than imposed on an abstract map family. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem normalized_actual_access_guide
    (hpublished : PublishedLoewnerBoundaryExtension)
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (hT : 0 < T)
    (hfresh : ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s)
    (α : ℝ → ℂ) {A tw : ℝ} (_hA : 0 < A) (htw : tw ∈ Ioc (0 : ℝ) A)
    (hα : ContinuousOn α (Icc 0 A)) (hiα : InjOn α (Icc 0 A))
    (hα0 : α 0 = γ T) (hαD : MapsTo α (Ioc 0 A) (survivingDomain γ T)) :
    ∃ c : ℝ, 0 < c ∧ ∃ (Fbar : ℂ → OnePoint ℂ) (β : ℝ → ℂ),
      ContinuousOn Fbar {z : ℂ | 0 ≤ z.im} ∧
      (∀ z ∈ upperHalfPlane, Fbar z = (F T ((U T : ℂ) + (c : ℂ) * z) : OnePoint ℂ)) ∧
      ContinuousOn β (Icc 0 A) ∧ InjOn β (Icc 0 A) ∧ β 0 = 0 ∧
      MapsTo β (Ioc 0 A) upperHalfPlane ∧
      (∀ t ∈ Icc 0 A, Fbar (β t) = (α t : OnePoint ℂ)) ∧
      ‖β tw‖ = 1 ∧
      (∀ t ∈ Ioc 0 A, β t = (G T (α t) - (U T : ℂ)) / (c : ℂ)) := by
  let D := survivingDomain γ T
  have htip : γ T ∉ D := by
    intro hh
    exact hh.1.2 ⟨T, ⟨bot_le, le_rfl⟩, rfl⟩
  have hlim := hw.fresh_tip_chart_tendsto hU hT hfresh
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
    exact ⟨(hw.2.2.2.1 T).continuousOn, fun _ => hlim⟩
  have hαS : MapsTo α (Icc 0 A) (insert (γ T) D) := by
    intro t ht
    by_cases ht0 : t = 0
    · simpa only [ht0, hα0] using mem_insert (γ T) D
    · exact mem_insert_of_mem _ (hαD ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩)
  have heval (t : ℝ) (ht : t ∈ Ioc 0 A) : gb (α t) = G T (α t) := by
    have hne : α t ≠ γ T := fun he => htip (he ▸ hαD ht)
    exact Function.update_of_ne hne _ _
  have hwayH : G T (α tw) - (U T : ℂ) ∈ upperHalfPlane := by
    have hh := hw.2.2.2.2.2.1 T (hαD htw)
    simpa only [upperHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im, sub_zero] using hh
  let c := ‖G T (α tw) - (U T : ℂ)‖
  have hc : 0 < c := norm_pos_iff.mpr (by
    intro he
    have hh : 0 < (G T (α tw) - (U T : ℂ)).im := hwayH
    rw [he] at hh
    exact (lt_irrefl 0) hh)
  let β : ℝ → ℂ := fun t => (gb (α t) - (U T : ℂ)) / (c : ℂ)
  have hβ : ContinuousOn β (Icc 0 A) :=
    ((hgb.comp hα hαS).sub continuousOn_const).div_const _
  have hβ0 : β 0 = 0 := by simp [β, gb, hα0]
  have hβeq (t : ℝ) (ht : t ∈ Ioc 0 A) :
      β t = (G T (α t) - (U T : ℂ)) / (c : ℂ) := by
    dsimp only [β]
    rw [heval t ht]
  have hβH : MapsTo β (Ioc 0 A) upperHalfPlane := by
    intro t ht
    rw [hβeq t ht]
    change 0 < ((G T (α t) - (U T : ℂ)) / (c : ℂ)).im
    rw [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact div_pos (hw.2.2.2.2.2.1 T (hαD ht)) hc
  obtain ⟨Fbar, hbar, hext, hbar0⟩ :=
    normalized_capacity_inverse_boundary_extension hpublished hU hw T c hc
  have hbarα (t : ℝ) (ht : t ∈ Icc 0 A) : Fbar (β t) = (α t : OnePoint ℂ) := by
    by_cases ht0 : t = 0
    · simpa only [ht0, hβ0, hα0] using hbar0
    · have ht' : t ∈ Ioc 0 A := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
      rw [hext _ (hβH ht'), hβeq t ht']
      have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
      have he : (U T : ℂ) + (c : ℂ) * ((G T (α t) - (U T : ℂ)) / (c : ℂ)) =
          G T (α t) := by field_simp; ring
      rw [he, hw.2.2.2.2.2.2.2.1 T (α t) (hαD ht')]
  have hβi : InjOn β (Icc 0 A) := by
    intro s hs t ht he
    apply hiα hs ht
    apply OnePoint.coe_injective
    rw [← hbarα s hs, ← hbarα t ht, he]
  have hβnorm : ‖β tw‖ = 1 := by
    rw [hβeq tw htw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    exact div_self hc.ne'
  exact ⟨c, hc, Fbar, β, hbar, hext, hβ, hβi, hβ0, hβH, hbarα, hβnorm, hβeq⟩

end SLEExactGauge

end

end OAI
