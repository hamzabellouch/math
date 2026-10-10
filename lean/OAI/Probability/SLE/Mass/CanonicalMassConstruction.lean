import OAI.Probability.SLE.Mass.CanonicalMassStoppingKernel
import OAI.Probability.SLE.Mass.CanonicalMassExhaustion

namespace OAI

/-! The first paper's canonical mass construction, including the exact
conditional kernel at arbitrary stopping times and terminal exhaustion. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

structure CanonicalMass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hBm : Measurable (Function.uncurry B))
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) where
  rational : RationalCanonicalMass P κ B hBm γ G
  process : ℝ≥0 → Ω → Measure upperHalfPlane
  progressive : IsProgressive (Filtration.natural B (fun r =>
    (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) process
  radon : ∀ t ω, (process t ω).Regular ∧ IsFiniteMeasureOnCompacts (process t ω)
  paths : ∀ᵐ ω ∂P, ContinuousMassPath (γ ω) (fun q => rational.mass q ω)
    (rational.terminal ω) (fun t => process t ω)
  exhaustion : ∀ᵐ ω ∂P, ∀ K : Set upperHalfPlane, IsCompact K →
    Tendsto (fun t : ℝ≥0 => (rational.terminal ω-process t ω) K) atTop (𝓝 0)
  kernel : ∀ S : Ω → WithTop ℝ≥0,
    ∀ hS : IsStoppingTime (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) S,
    ∀ E : Set Ω, MeasurableSet[hS.measurableSpace] E →
      (P.restrict E).bind rational.terminal =
        (P.restrict E).bind (fun ω => extendedCanonicalMass process rational.terminal (S ω) ω) +
        (P.restrict E).bind (halfPlaneStoppingGreenMeasure κ B γ G S)

/-- Proposition `mass:construction` of the first manuscript. The sole
published input is the disk-growth consequence of Duren (1983), §2.3;
all stochastic estimates and limiting arguments are proved here. -/
theorem exists_canonicalMass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) :
    Nonempty (CanonicalMass P κ B hBm γ G) := by
  obtain ⟨C⟩ := exists_rationalCanonicalMass hB
    (fun t => hBm.comp (measurable_const.prodMk measurable_id)) hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
  obtain ⟨N,hNp,hNr,hpath⟩ := C.exists_continuous_progressive_extension (fun ω => (hw ω).1)
  exact ⟨{
    rational := C
    process := N
    progressive := hNp
    radon := hNr
    paths := hpath
    exhaustion := C.finite_times_exhaust_terminal hB hBm hBc hB0 hκ hκ8 γ G F hw N hpath
    kernel := C.stopping_conditional_kernel hB hBm hBc hB0 hκ hκ8 F hw hgrowth N hNp hNr hpath }⟩

end SLEExactGauge.Multipoint

namespace SLEExactGauge

/-- The canonical mass main construction for an ordinary SLE in its
regular Brownian presentation, on its full-measure sample space. -/
theorem RegularSLEPresentation.canonical_mass_main
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hgrowth : PublishedDiskUnivalentGrowth) :
    Nonempty (Multipoint.CanonicalMass (P.comap (Subtype.val : a.samples → Ω)) κ a.B
      (measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B)
      (fun ω => γ ω) a.G) :=
  Multipoint.exists_canonicalMass a.brownian
    (measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B)
    a.continuous_B a.zero_B hκ hκ8 (fun ω => γ ω) a.G a.F a.witness hgrowth

end SLEExactGauge

end

end OAI
