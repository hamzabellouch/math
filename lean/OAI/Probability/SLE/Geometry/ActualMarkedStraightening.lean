import OAI.Probability.SLE.Geometry.CompleteAccessGuide

namespace OAI

/-! Straighten the actual complete marked access guide. The local chart's
zero set is identified with the explicit physical guide, including the
exclusion of every nonlocal guide piece. -/

noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SLEExactGauge

/-- An actual fresh-tip guide and its local marked-point chart give a
straightening with an exact physical zero set. -/
theorem actual_marked_access_straightening
    (hpublished : PublishedHalfPlaneCrosscutStraightening)
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (T : ℝ≥0) (hT : 0 < T)
    (hfresh : ∀ s : ℝ≥0, s < T → γ T ∈ survivingDomain γ s)
    (α : ℝ≥0 → ℂ) (hα : Continuous α) (hiα : Function.Injective α)
    (hα0 : α 0 = γ T) (hαD : ∀ t : ℝ≥0, 0 < t → α t ∈ survivingDomain γ T)
    (hescape : Tendsto α atTop (cocompact ℂ))
    (Q : ℂ ≃ₜ ℂ) (r : ℝ)
    (hQD : MapsTo Q (ball 0 r) (survivingDomain γ T))
    (hlocus : ∀ z ∈ ball (0 : ℂ) r,
      (∃ t : ℝ≥0, 0 < t ∧ α t = Q z) ↔ z.im = 0) :
    ∃ h : ℂ ≃ₜ ℂ, (∀ x : ℝ, h (x : ℂ) = (x : ℂ)) ∧
      MapsTo h upperHalfPlane upperHalfPlane ∧
      (∀ z ∈ survivingDomain γ T,
        (h (G T z - (U T : ℂ))).re = 0 ↔ ∃ t : ℝ≥0, 0 < t ∧ α t = z) ∧
      ContinuousOn (fun z => h (G T (Q z) - (U T : ℂ))) (ball 0 r) ∧
      InjOn (fun z => h (G T (Q z) - (U T : ℂ))) (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) r, (h (G T (Q z) - (U T : ℂ))).re = 0 ↔ z.im = 0 := by
  obtain ⟨β, hc, hi, hz, hH, hproper, heq⟩ :=
    actual_complete_access_guide hw hU T hT hfresh α hα hiα hα0 hαD hescape
  obtain ⟨h, hreal, hhalf, hstraight⟩ := hpublished β hc hi hz hH hproper
  have hzero (z : ℂ) (hzD : z ∈ survivingDomain γ T) :
      (h (G T z - (U T : ℂ))).re = 0 ↔ ∃ t : ℝ≥0, 0 < t ∧ α t = z := by
    have hzH : G T z - (U T : ℂ) ∈ upperHalfPlane := by
      simpa only [upperHalfPlane, mem_ofPred_eq, Complex.sub_im, Complex.ofReal_im, sub_zero]
        using hw.imag_positive T z hzD
    rw [CrosscutSides.straightened_real_zero_iff β h hhalf hstraight hzH]
    constructor
    · rintro ⟨t, ht, he⟩
      rw [heq t ht] at he
      have hg : G T (α t) = G T z := sub_left_inj.mp he
      refine ⟨t, ht, ?_⟩
      calc
        α t = F T (G T (α t)) := (hw.2.2.2.2.2.2.2.1 T _ (hαD t ht)).symm
        _ = F T (G T z) := congrArg (F T) hg
        _ = z := hw.2.2.2.2.2.2.2.1 T _ hzD
    · rintro ⟨t, ht, he⟩
      exact ⟨t, ht, by rw [heq t ht, he]⟩
  refine ⟨h, hreal, hhalf, hzero, ?_, ?_, ?_⟩
  · exact h.continuous.comp_continuousOn
      (((hw.2.2.2.1 T).continuousOn.comp Q.continuous.continuousOn hQD).sub continuousOn_const)
  · intro z hz' w hw' he
    have hg : G T (Q z) = G T (Q w) := sub_left_inj.mp (h.injective he)
    apply Q.injective
    calc
      Q z = F T (G T (Q z)) := (hw.2.2.2.2.2.2.2.1 T _ (hQD hz')).symm
      _ = F T (G T (Q w)) := congrArg (F T) hg
      _ = Q w := hw.2.2.2.2.2.2.2.1 T _ (hQD hw')
  · intro z hz'
    exact (hzero (Q z) (hQD hz')).trans (hlocus z hz')

end SLEExactGauge

end

end OAI
