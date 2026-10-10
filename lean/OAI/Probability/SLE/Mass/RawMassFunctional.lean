import OAI.Probability.SLE.Stochastic.DriverPastFactorization
import OAI.Probability.SLE.Mass.RationalTraceMassProgressiveVersion

namespace OAI

/-! A fixed raw, nonanticipating mass functional on continuous driver paths.
Each rational slice is first factored through the stopped driver, and the
single rational reconstruction is progressive on the full path space. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal CompactlySupported

namespace SLEExactGauge

local instance rawMassDriverMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawMassDriverBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma raw_rational_reconstruction_depends_on_past
    (F : ℚ → C(ℝ≥0,ℝ) → Measure upperHalfPlane)
    (t : ℝ≥0) (p q : C(ℝ≥0,ℝ)) (hpq : ∀ s ≤ t, p s=q s) :
    rationalRadonExtension (fun r p => F r (driverPathStopped (r:ℝ).toNNReal p)) t p =
      rationalRadonExtension (fun r p => F r (driverPathStopped (r:ℝ).toNNReal p)) t q := by
  unfold rationalRadonExtension
  apply congrArg canonicalRadonLimit
  funext n
  apply congrArg (F (leftRationalSample n t))
  exact driverPathStopped_eq_of_agree t _ (by
    simpa only [Real.toNNReal_coe] using
      Real.toNNReal_le_toNNReal (leftRationalSample_le n t)) p q hpq

theorem exists_raw_progressive_radon_factor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (N : ℝ≥0 → Ω → Measure upperHalfPlane)
    (hNm : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) N)
    (hNr : ∀ t ω, (N t ω).Regular)
    (hNc : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂N t ω)) :
    ∃ R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane,
      IsProgressive driverPathFiltration R ∧
      (∀ t p, (R t p).Regular ∧ IsFiniteMeasureOnCompacts (R t p)) ∧
      (∀ t p q, (∀ s ≤ t, p s=q s) → R t p=R t q) ∧
      ∀ᵐ ω ∂P, ∀ t, R t (sourceDriverPath B hc ω) = N t ω := by
  choose F hFm hFr hFe using fun q : ℚ => exists_stopped_driver_radon_factor B hm hc
    (q:ℝ).toNNReal (N (q:ℝ).toNNReal) (hNr _) (hNm _)
  let μ (q : ℚ) (p : C(ℝ≥0,ℝ)) := F q (driverPathStopped (q:ℝ).toNNReal p)
  have hμr (q : ℚ) (p : C(ℝ≥0,ℝ)) : (μ q p).Regular := hFr q _
  have hμm (q : ℚ) (_hq : 0 ≤ q) :
      Measurable[driverPathFiltration (q:ℝ).toNNReal] (μ q) :=
    (hFm q).comp (driverPathStopped_measurable_past (q:ℝ).toNNReal)
  refine ⟨rationalRadonExtension μ,rationalRadonExtension_progressive
    driverPathFiltration μ hμr hμm,rationalRadonExtension_regular μ,
      raw_rational_reconstruction_depends_on_past F,?_⟩
  let μ' (q : ℚ) (ω : Ω) := μ q (sourceDriverPath B hc ω)
  have hcont : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Continuous (fun t : ℝ => ∫ z, f z ∂N t.toNNReal ω) := by
    filter_upwards [hNc] with ω hω
    intro f
    exact (hω f).comp continuous_real_toNNReal
  have heq : ∀ᵐ ω ∂P, ∀ q : ℚ, N (q:ℝ).toNNReal ω = μ' q ω :=
    ae_of_all _ (fun ω q => (hFe q ω).symm)
  have he := rationalRadonExtension_common_version P μ' (fun t ω => N t.toNNReal ω)
    (fun t ω => hNr t.toNNReal ω) hcont heq
  filter_upwards [he] with ω hω
  intro t
  simpa only [rationalRadonExtension,μ',Real.toNNReal_coe] using hω t

end SLEExactGauge

end

end OAI
