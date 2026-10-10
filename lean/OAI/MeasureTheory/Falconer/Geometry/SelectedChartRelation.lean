import OAI.MeasureTheory.Falconer.Angular.GnomonicPrunedLaw
import OAI.MeasureTheory.Falconer.Estimates.PlanarSelectedGain
import OAI.MeasureTheory.Falconer.Slicing.GaussianBandRestriction

namespace OAI

/-! # The selected incidence in its original affine chart labels -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {n h : ℕ} {ι κ : Type*}

def selectedChartRelation (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (J : Sphere (n+1) → Finset κ)
    (a : κ → Space (n+1)) (R T : ℝ) : Set (Space (n+1) × Space n) :=
  {u | (u.1,gnomonicChart u.2) ∈ selectedActiveRelation A z δ E J a R T ∧ ‖u.2‖ ≤ 1}

theorem selectedChartRelation_measurable [Fintype κ] [DecidableEq κ]
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) (R T : ℝ) :
    MeasurableSet (selectedChartRelation A z δ E J a R T) := by
  have hm : Measurable (fun u : Space (n+1) × Space n => (u.1,gnomonicChart u.2)) :=
    measurable_fst.prodMk ((gnomonicChart_continuous n).measurable.comp measurable_snd)
  have hn : MeasurableSet {u : Space (n+1) × Space n | ‖u.2‖ ≤ 1} :=
    measurableSet_le (measurable_norm.comp measurable_snd) measurable_const
  exact ((selectedActiveRelation_measurable A z δ E hE J hJ a R T).preimage hm).inter hn

theorem selected_chart_incidence_eq [Fintype ι] [Fintype κ] [DecidableEq κ]
    (μ : Measure (Space (n+1))) (ν₀ : Measure (Space n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν₀]
    (hν₀ : ∀ᵐ p ∂ν₀, ‖p‖ ≤ 1)
    (A : Fin h → Space (n+1)) (z : Space h) (δ : ℝ)
    (r : ι → ℝ) (TP TD : ι → ℝ≥0∞) (M : ℝ≥0∞)
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    (J : Sphere (n+1) → Finset κ) (hJ : ∀ i, MeasurableSet {w | i ∈ J w})
    (a : κ → Space (n+1)) (R T : ℝ) :
    let α := (gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))
    let β := (gaussianChartSliceMeasure ν₀ A δ).restrict
      (gnomonicChart ⁻¹' gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r TD M A)
    (α.prod β) (selectedChartRelation A z δ E J a R T) =
      gaussianPrunedPairMass μ (Measure.map gnomonicChart ν₀) δ r TP TD M
        (gaussianActiveRelation E J a R (ENNReal.ofReal T) true) (A,z) := by
  intro α β
  have hD : MeasurableSet (gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r TD M A) :=
    gaussianDirectionGood_measurable_fixed (Measure.map (gnomonicChart : Space n → Sphere (n+1)) ν₀) δ r TD M A
  have hm : Measure.map gnomonicChart β =
      (gaussianDirectionSliceMeasure (Measure.map gnomonicChart ν₀) A δ).restrict
        (gaussianDirectionGood (Measure.map gnomonicChart ν₀) δ r TD M A) :=
    gnomonic_restricted_slice_map ν₀ A δ _ hD
  have hnorm : ∀ᵐ p ∂β, ‖p‖ ≤ 1 :=
    ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_of_ae hν₀) _)
  have heq : (α.prod β) (selectedChartRelation A z δ E J a R T) =
      (α.prod β) {u | (u.1,gnomonicChart u.2) ∈ selectedActiveRelation A z δ E J a R T} := by
    apply measure_congr
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hnorm] with u hu
    exact propext ⟨fun hx => hx.1,fun hx => ⟨hx,hu⟩⟩
  rw [heq,gnomonic_incidence_transport α β _ (selectedActiveRelation_measurable A z δ E hE J hJ a R T),hm]
  change gaussianPrunedIncidence μ (Measure.map gnomonicChart ν₀) δ r TP TD M
    (selectedActiveRelation A z δ E J a R T) (A,z) = _
  exact gaussian_pruned_incidence_inter_bands μ (Measure.map gnomonicChart ν₀) δ r TP TD M _ (A,z)

end Falconer

end OAI
