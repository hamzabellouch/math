import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.HeightPairingOuterLimit

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

theorem integral_outer_regions_exhaustion {d : ℕ}
    (ρ : Measure (Ambient d × Ambient d)) (a : Ambient d) (s : ℕ → Set (Ambient d))
    (hs : ∀ H, MeasurableSet (s H))
    (hcontain : ∀ R : ℝ, ∀ᶠ H in atTop, ball a R ⊆ s H)
    (F : Ambient d × Ambient d → ℝ) (hF : Integrable F ρ) :
    Tendsto (fun H => ∫ q in univ ×ˢ s H, F q ∂ρ) atTop (𝓝 (∫ q, F q ∂ρ)) := by
  let G := fun H => (univ ×ˢ s H).indicator F
  have hGmeas : ∀ H, AEStronglyMeasurable (G H) ρ :=
    fun H => hF.aestronglyMeasurable.indicator (MeasurableSet.univ.prod (hs H))
  have hGbound : ∀ H, ∀ᵐ q ∂ρ, ‖G H q‖ ≤ ‖F q‖ := by
    intro H
    apply Eventually.of_forall
    intro q
    by_cases hq : q ∈ univ ×ˢ s H
    · simp only [G, indicator_of_mem hq, le_refl]
    · simp only [G, indicator_of_notMem hq, norm_zero, norm_nonneg]
  have hGlim : ∀ᵐ q ∂ρ, Tendsto (fun H => G H q) atTop (𝓝 (F q)) := by
    apply Eventually.of_forall
    intro q
    apply tendsto_const_nhds.congr'
    filter_upwards [hcontain (dist q.2 a + 1)] with H hH
    have hq : q ∈ univ ×ˢ s H :=
      ⟨mem_univ _, hH (by change dist q.2 a < dist q.2 a + 1; linarith)⟩
    exact (indicator_of_mem hq F).symm
  have ht := tendsto_integral_of_dominated_convergence (fun q => ‖F q‖) hGmeas hF.norm hGbound hGlim
  simpa only [G, integral_indicator (MeasurableSet.univ.prod (hs _))] using! ht

theorem heightPairingOn_as_exhaustion {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d)
    (A : Set (Ambient d)) (hA : MeasurableSet A) (r T : ℝ) (hr : 0 < r)
    (hinner : ball a r ⊆ A) (houter : A ⊆ ball a T)
    (s : ℕ → Set (Ambient d)) (hs : ∀ H, MeasurableSet (s H))
    [∀ H, IsFiniteMeasure (μ.restrict (s H))]
    (hcontain : ∀ R : ℝ, ∀ᶠ H in atTop, ball a R ⊆ s H)
    (w φ : Ambient d → ℝ) (hφI : Integrable φ μ) (hφzero : ∀ x ∉ A, φ x = 0)
    (hmean : (∫ x, φ x ∂μ) = 0)
    (hw : ∀ H, Integrable w (μ.restrict (s H)))
    (hF : ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      ((μ.restrict (s H)).prod (μ.restrict (s H))))
    (hfar : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict A).prod (μ.restrict Aᶜ))) :
    Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear m w φ q.1 q.2 ∂(μ.restrict (s H)).prod (μ.restrict (s H))))
      atTop (𝓝 (heightPairingOn m μ a A w φ)) := by
  have ht := integral_outer_regions_exhaustion ((μ.restrict A).prod (μ.restrict Aᶜ))
    a s hs hcontain (renormalizedNormalIntegrand m w φ a) hfar
  have hlim : Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear m w φ q.1 q.2 ∂(μ.restrict A).prod (μ.restrict A)) +
      ∫ q in univ ×ˢ s H, renormalizedNormalIntegrand m w φ a q
        ∂(μ.restrict A).prod (μ.restrict Aᶜ)) atTop (𝓝 (heightPairingOn m μ a A w φ)) :=
    tendsto_const_nhds.add ht
  apply hlim.congr'
  filter_upwards [hcontain T] with H hH
  have hAs : A ⊆ s H := houter.trans hH
  have hrestrict : (μ.restrict (s H)).restrict A = μ.restrict A := by
    rw [Measure.restrict_restrict hA, inter_eq_left.mpr hAs]
  have hmeanA : (∫ x in A, φ x ∂μ.restrict (s H)) = 0 := by
    rw [hrestrict]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hφzero).trans hmean
  have hfinite := (finite_height_pairing_eq_renormalized m w φ (μ.restrict (s H)) a A hA
    hφI.restrict hφzero hmeanA
    (center_height_integrable_finite_region m (μ.restrict (s H)) w (hw H) a r hr A hA hinner)
    (hF H)).2
  have hcomm : (μ.restrict (s H)).restrict Aᶜ = (μ.restrict Aᶜ).restrict (s H) := by
    rw [Measure.restrict_restrict hA.compl, Measure.restrict_restrict (hs H), inter_comm]
  have hprod : (μ.restrict A).prod ((μ.restrict Aᶜ).restrict (s H)) =
      ((μ.restrict A).prod (μ.restrict Aᶜ)).restrict (univ ×ˢ s H) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  unfold heightPairingOn at hfinite
  rw [hrestrict, hcomm, hprod] at hfinite
  exact hfinite.symm

theorem heightPairingOn_zero_of_exhaustion {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [SFinite μ] (a : Ambient d)
    (A : Set (Ambient d)) (hA : MeasurableSet A) (r T : ℝ) (hr : 0 < r)
    (hinner : ball a r ⊆ A) (houter : A ⊆ ball a T)
    (s : ℕ → Set (Ambient d)) (hs : ∀ H, MeasurableSet (s H))
    [∀ H, IsFiniteMeasure (μ.restrict (s H))]
    (hcontain : ∀ R : ℝ, ∀ᶠ H in atTop, ball a R ⊆ s H)
    (w φ : Ambient d → ℝ) (hφI : Integrable φ μ) (hφzero : ∀ x ∉ A, φ x = 0)
    (hmean : (∫ x, φ x ∂μ) = 0)
    (hw : ∀ H, Integrable w (μ.restrict (s H)))
    (hF : ∀ H, Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      ((μ.restrict (s H)).prod (μ.restrict (s H))))
    (hfar : Integrable (renormalizedNormalIntegrand m w φ a) ((μ.restrict A).prod (μ.restrict Aᶜ)))
    (hzero : Tendsto (fun H => (1 / 2 : ℝ) * (∫ q : Ambient d × Ambient d,
      fractionalBilinear m w φ q.1 q.2 ∂(μ.restrict (s H)).prod (μ.restrict (s H)))) atTop (𝓝 0)) :
    heightPairingOn m μ a A w φ = 0 :=
  tendsto_nhds_unique (heightPairingOn_as_exhaustion m μ a A hA r T hr hinner houter
    s hs hcontain w φ hφI hφzero hmean hw hF hfar) hzero

end

end RieszRectifiability

end OAI
