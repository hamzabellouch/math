import OAI.Probability.FreeIsing.Brownian.Martingale
import OAI.Probability.FreeIsing.Estimates.IndependentEnlargement
import OAI.Probability.FreeIsing.Martingales.InnovationMartingale

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

def brownianSignalFiltration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, StronglyMeasurable (B t))
    (σ : Ω → ℝ) (hσ : Measurable σ) : Filtration ℝ≥0 mΩ :=
  Filtration.natural B hm ⊔ Filtration.const ℝ≥0 (MeasurableSpace.comap σ inferInstance) hσ.comap_le

theorem preBrownian_martingale_signalFiltration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t)) {σ : Ω → ℝ} (hσ : Measurable σ)
    (hind : IndepFun (fun ω t => B t ω) σ P) :
    Martingale B (brownianSignalFiltration B hm σ hσ) P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hfull : Measurable (fun ω t => B t ω) := Measurable.of_eval (fun t => (hm t).measurable)
  have hcoord (t : ℝ≥0) :
      @Measurable Ω ℝ (MeasurableSpace.comap (fun ω t => B t ω) inferInstance) inferInstance (B t) :=
    by
      have harray : @Measurable Ω (ℝ≥0 → ℝ)
          (MeasurableSpace.comap (fun ω t => B t ω) inferInstance) inferInstance
          (fun ω t => B t ω) := measurable_iff_comap_le.mpr le_rfl
      exact (show Measurable (fun f : ℝ≥0 → ℝ => f t) from measurable_pi_apply t).comp harray
  have hNat (t : ℝ≥0) : Filtration.natural B hm t ≤
      MeasurableSpace.comap (fun ω t => B t ω) inferInstance := by
    change (⨆ s ≤ t, MeasurableSpace.comap (B s) inferInstance) ≤ _
    exact iSup₂_le fun s _ => (hcoord s).comap_le
  exact martingale_independent_enlargement hfull.comap_le hσ.comap_le hNat hind
    (preBrownian_martingale_natural hB hm)

def plantedObservation {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := B t ω + (t : ℝ) * σ ω

theorem plantedObservation_stronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, StronglyMeasurable (B t)) {σ : Ω → ℝ} (hσ : Measurable σ) (t : ℝ≥0) :
    StronglyMeasurable (plantedObservation B σ t) :=
  (hm t).add (stronglyMeasurable_const.mul hσ.stronglyMeasurable)

def observationFiltration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, StronglyMeasurable (B t))
    (σ : Ω → ℝ) (hσ : Measurable σ) : Filtration ℝ≥0 mΩ :=
  Filtration.natural (plantedObservation B σ) (plantedObservation_stronglyMeasurable hm hσ)

theorem naturalFiltration_le_of_stronglyAdapted
    {Ω ι : Type*} [Preorder ι] [mΩ : MeasurableSpace Ω]
    {X : ι → Ω → ℝ} (hm : ∀ t, StronglyMeasurable (X t))
    {G : Filtration ι mΩ} (had : StronglyAdapted G X) :
    Filtration.natural X hm ≤ G := by
  intro t
  change (⨆ s ≤ t, MeasurableSpace.comap (X s) inferInstance) ≤ G t
  exact iSup₂_le fun s hst => ((had s).mono (G.mono hst)).measurable.comap_le

theorem observationFiltration_le_signalFiltration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, StronglyMeasurable (B t)) {σ : Ω → ℝ} (hσ : Measurable σ) :
    observationFiltration B hm σ hσ ≤ brownianSignalFiltration B hm σ hσ := by
  apply naturalFiltration_le_of_stronglyAdapted
  intro t
  have hBt : StronglyMeasurable[brownianSignalFiltration B hm σ hσ t] (B t) :=
    (Filtration.stronglyAdapted_natural hm t).mono le_sup_left
  have hσm : StronglyMeasurable[MeasurableSpace.comap σ inferInstance] σ :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hσG : StronglyMeasurable[brownianSignalFiltration B hm σ hσ t] σ :=
    hσm.mono le_sup_right
  exact hBt.add (stronglyMeasurable_const.mul hσG)

theorem preBrownian_observation_innovation_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B m : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, StronglyMeasurable (B t)) {σ : Ω → ℝ}
    (hσ : Measurable σ) (hσint : Integrable σ P)
    (hind : IndepFun (fun ω t => B t ω) σ P)
    (hmAd : StronglyAdapted (observationFiltration B hmB σ hσ) m)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | observationFiltration B hmB σ hσ t])
    (hAad : StronglyAdapted (observationFiltration B hmB σ hσ) (nnrealTimePrimitive m))
    (hInt : ∀ s t : ℝ≥0, s ≤ t →
      Integrable (fun p : ℝ × Ω => m p.1.toNNReal p.2)
        ((volume.restrict (Set.Ioc (s : ℝ) (t : ℝ))).prod P)) :
    Martingale (fun t ω => plantedObservation B σ t ω - nnrealTimePrimitive m t ω)
      (observationFiltration B hmB σ hσ) P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact compensated_observation_martingale_of_posterior_version
    (preBrownian_martingale_signalFiltration hB hmB hσ hind)
    (observationFiltration_le_signalFiltration hmB hσ) hσint
    (Filtration.stronglyAdapted_natural (plantedObservation_stronglyMeasurable hmB hσ))
    hmAd hposterior hAad hInt

end Problem367

end OAI
