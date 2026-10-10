import OAI.Probability.SLE.Mass.RadonFactorization
import OAI.Probability.SLE.StoppedMeasures
import OAI.Probability.SLE.Mass.RationalTraceMassAdapted

namespace OAI

/-! Real continuous driver prefixes realize the natural filtration.
Radon kernels adapted to that filtration factor through each stopped prefix. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal CompactlySupported

namespace SLEExactGauge

local instance driverPastPathMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance driverPastPathBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def driverPathStopped (t : ℝ≥0) (p : C(ℝ≥0,ℝ)) : C(ℝ≥0,ℝ) :=
  ⟨fun s => p (min s t),p.continuous.comp (continuous_id.min continuous_const)⟩

def driverPathFiltration : Filtration ℝ≥0 (borel C(ℝ≥0,ℝ)) :=
  Filtration.natural (fun t (p : C(ℝ≥0,ℝ)) => p t)
    (fun t => (continuous_eval_const t).measurable.stronglyMeasurable)

lemma driverPathStopped_eq_of_agree (T t : ℝ≥0) (ht : t ≤ T)
    (p q : C(ℝ≥0,ℝ)) (hpq : ∀ s ≤ T, p s=q s) :
    driverPathStopped t p = driverPathStopped t q := by
  ext s
  exact hpq (min s t) ((min_le_right s t).trans ht)

lemma driverPathStopped_measurable_past (t : ℝ≥0) :
    Measurable[driverPathFiltration t] (driverPathStopped t) := by
  have he (s : ℝ≥0) : Measurable[driverPathFiltration t]
      (fun p : C(ℝ≥0,ℝ) => p (min s t)) := by
    have hm (r : ℝ≥0) : StronglyMeasurable (fun p : C(ℝ≥0,ℝ) => p r) :=
      (continuous_eval_const r).measurable.stronglyMeasurable
    have h := (Filtration.stronglyAdapted_natural hm) (min s t)
    exact (h.mono (driverPathFiltration.mono (min_le_right s t))).measurable
  exact @source_path_measurable C(ℝ≥0,ℝ) ℝ (driverPathFiltration t)
    _ _ _ _ (borel _) driverPastPathBorel _ (driverPathStopped t) he

lemma natural_le_stoppedDriverPath_comap
    {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω)) (t : ℝ≥0) :
    (Filtration.natural B (fun r => (hm r).stronglyMeasurable)) t ≤
      MeasurableSpace.comap (fun ω => driverPathStopped t (sourceDriverPath B hc ω)) (borel _) := by
  have hb (s : ℝ≥0) (hs : s ≤ t) :
      Measurable[MeasurableSpace.comap (fun ω => driverPathStopped t (sourceDriverPath B hc ω))
        (borel C(ℝ≥0,ℝ))] (B s) := by
    have h := (continuous_eval_const s).measurable.comp
      (Measurable.of_comap_le (le_refl (MeasurableSpace.comap
        (fun ω => driverPathStopped t (sourceDriverPath B hc ω)) (borel C(ℝ≥0,ℝ)))))
    convert h using 1
    funext ω
    simp only [Function.comp_def,driverPathStopped,sourceDriverPath,ContinuousMap.coe_mk,min_eq_left hs]
  change (⨆ s ≤ t, MeasurableSpace.comap (B s) (borel ℝ)) ≤ _
  exact iSup_le fun s => iSup_le fun hs => measurable_iff_comap_le.mp (hb s hs)

lemma exists_stopped_driver_radon_factor
    {Ω : Type*} [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ)
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (t : ℝ≥0) (N : Ω → Measure upperHalfPlane) (hNr : ∀ ω, (N ω).Regular)
    (hNm : Measurable[(Filtration.natural B (fun r => (hm r).stronglyMeasurable)) t] N) :
    ∃ R : C(ℝ≥0,ℝ) → Measure upperHalfPlane, Measurable R ∧
      (∀ p, (R p).Regular) ∧ ∀ ω, R (driverPathStopped t (sourceDriverPath B hc ω)) = N ω := by
  apply (localTestFamily upperHalfPlane).measurable_radon_factor
    (fun ω => driverPathStopped t (sourceDriverPath B hc ω)) N hNr
  intro j
  have ht := @measurable_halfPlane_compact_test_integral Ω
    ((Filtration.natural B (fun r => (hm r).stronglyMeasurable)) t)
    N hNm hNr ((localTestFamily upperHalfPlane).test j)
  exact ht.mono (natural_le_stoppedDriverPath_comap B hm hc t) le_rfl

end SLEExactGauge

end

end OAI
