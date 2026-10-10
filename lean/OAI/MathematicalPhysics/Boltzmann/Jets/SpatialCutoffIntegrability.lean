import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability

namespace OAI

/-! # Removing small spatial regions in the collision-integrability argument -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν]

def outerCutoff (S : Set X) (f : X × Y → ℝ) : X × Y → ℝ :=
  (Prod.fst ⁻¹' Sᶜ).indicator f

theorem spatial_cutoff_error {f : X × Y → ℝ} {G : X → ℝ≥0∞} {S : Set X}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (hS : MeasurableSet S)
    (hG : ∀ᵐ x ∂μ, (∫⁻ y, ENNReal.ofReal (f (x,y)) ∂ν) ≤ G x) :
    eLpNorm (fun z => f z-outerCutoff S f z) 1 (μ.prod ν) ≤ ∫⁻ x in S, G x ∂μ := by
  let g := (Prod.fst ⁻¹' S).indicator f
  have hm : Measurable g := hfm.indicator (hS.preimage measurable_fst)
  have hn (z) : 0 ≤ g z := indicator_nonneg (fun z _ => hf z) z
  have he : (fun z => f z-outerCutoff S f z) = g := by
    funext z
    by_cases hz : z.1 ∈ S <;> simp [outerCutoff,g,hz]
  rw [he,eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable]
  simp_rw [Real.enorm_eq_ofReal (hn _)]
  have hme : Measurable (fun z => ENNReal.ofReal (g z)) := ENNReal.measurable_ofReal.comp hm
  rw [lintegral_prod (fun z => ENNReal.ofReal (g z)) hme.aemeasurable,
    ← lintegral_indicator hS]
  apply lintegral_mono_ae
  filter_upwards [hG] with x hx
  by_cases hs : x ∈ S
  · have hg (y : Y) : g (x,y) = f (x,y) := indicator_of_mem (show (x,y) ∈ Prod.fst ⁻¹' S from hs) f
    simp_rw [hg]
    rw [indicator_of_mem hs]
    exact hx
  · have hg (y : Y) : g (x,y) = 0 := indicator_of_notMem (show (x,y) ∉ Prod.fst ⁻¹' S from hs) f
    simp_rw [hg,ENNReal.ofReal_zero]
    rw [indicator_of_notMem hs,lintegral_zero]

theorem uniformIntegrable_of_spatial_cutoffs {f : ℕ → X × Y → ℝ}
    {G : X → ℝ≥0∞} {S : ℕ → Set X}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hS : ∀ j, MeasurableSet (S j))
    (hG : ∀ n, ∀ᵐ x ∂μ, (∫⁻ y, ENNReal.ofReal (f n (x,y)) ∂ν) ≤ G x)
    (hout : ∀ j, UniformIntegrable (fun n => outerCutoff (S j) (f n)) 1 (μ.prod ν))
    (hsmall : Tendsto (fun j => ∫⁻ x in S j, G x ∂μ) atTop (𝓝 0)) :
    UniformIntegrable f 1 (μ.prod ν) := by
  apply uniformIntegrable_of_approximation hout
  intro ε hε
  have hev : ∀ᶠ j in atTop, (∫⁻ x in S j, G x ∂μ) ≤ ε :=
    (hsmall.eventually (gt_mem_nhds hε)).mono (fun _ h => h.le)
  obtain ⟨j,hj⟩ := hev.exists
  exact ⟨j,fun n => (spatial_cutoff_error (hfm n) (hf n) (hS j) (hG n)).trans hj⟩

end BoltzmannNonuniqueness.Compactness

end

end OAI
