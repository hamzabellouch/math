import OAI.Probability.SLE.Stochastic.DriverLawKernelTransfer
import OAI.Probability.SLE.Stochastic.ScaledDriverFiltration
import OAI.Probability.SLE.Loewner.RawRestartGreenKernel

namespace OAI

/-! The raw canonical mass kernel under Brownian scaling, conditioned on
the full original past at the corresponding physical time. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint

local instance rawScaledGreenMeasurable : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance rawScaledGreenBorel : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}

lemma CanonicalMass.raw_scaled_green_kernel
    (C : CanonicalMass P κ B hBm γ G) (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω))
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (R : RawCanonicalMass)
    (he : ∀ᵐ ω ∂P, (∀ t, R.process t (sourceDriverPath B hc ω)=C.process t ω) ∧
      R.terminal (sourceDriverPath B hc ω)=C.rational.terminal ω)
    (c : ℝ≥0) (hcp : 0 < c) (t : ℝ≥0) (E : Set Ω)
    (hE : MeasurableSet[(Filtration.natural B (fun s =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B s)).stronglyMeasurable)) t] E) :
    let Y := sourceDriverPath (scaledBrownianDriver c B) (scaledBrownianDriver_continuous c B hc)
    (P.restrict E).bind (fun ω => R.terminal (Y ω))=
      (P.restrict E).bind (fun ω => R.process (c^2*t) (Y ω)+
        canonicalGreenMass κ (c^2*t) (Y ω)) := by
  dsimp only
  have hm (s : ℝ≥0) : Measurable (B s) := hBm.comp (measurable_const.prodMk measurable_id)
  apply source_driver_bind_of_same_law_kernel hB (scaledBrownianDriver_brownian c hcp hB)
    hm (scaledBrownianDriver_measurable c B hm) hc (scaledBrownianDriver_continuous c B hc)
    (scaledBrownianDriver_path_law c hcp B hB hm hc).symm (c^2*t)
    R.terminal (fun p => R.process (c^2*t) p+canonicalGreenMass κ (c^2*t) p)
    R.terminal_measurable
    ((R.progressive.adapted (c^2*t)).add (canonicalGreenMass_measurable_past κ (c^2*t)))
    (fun A hA => C.raw_green_kernel hc F hw R he (c^2*t) A hA) E
  rwa [scaledBrownianDriver_filtration c hcp B hm t]

end SLEExactGauge.Multipoint

end

end OAI
