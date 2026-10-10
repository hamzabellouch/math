import OAI.Probability.SLE.Mass.CanonicalMassFirstVisit
import OAI.Probability.SLE.Loewner.TraceRestrictionContinuity

namespace OAI

/-! The first-visit identity holds on one event simultaneously at every
finite time. In particular later returns carry no previously assigned mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem CanonicalMass.all_times_eq_restrict_past
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8)
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (C : CanonicalMass P κ B hBm γ G) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, C.process t ω = (C.rational.terminal ω).restrict
      {z : upperHalfPlane | (z:ℂ) ∈ γ ω '' Icc 0 t} := by
  have hq (q : ℚ) := C.atTime_eq_restrict_past hB hBm hBc hB0 hκ hκ8 F hw (q:ℝ).toNNReal
  have hlim := C.rational.all_finite_times_limit hBc hκ hκ8 F hw C.process C.radon C.paths
  filter_upwards [ae_all_iff.mpr hq,C.paths,hlim] with ω hq hp hl
  let : (C.rational.terminal ω).Regular := (C.rational.terminal_radon ω).1
  have hpast (t : ℝ≥0) : C.process t ω {z : upperHalfPlane | (z:ℂ) ∉ γ ω '' Icc 0 t} = 0 := by
    let : (C.process t ω).Regular := (C.radon t ω).1
    exact convex_level_radon_limit_carried_by_past ω (hBc ω) (hw ω) t (fun n => (n:ℝ))
      tendsto_natCast_atTop_atTop C.rational.supports C.rational.weights (C.process t ω) (hl t)
  apply trace_restriction_of_rational_times (γ ω) (hw ω).1 (fun q => C.rational.mass q ω)
    (C.rational.terminal ω) (fun t => C.process t ω) hp hpast
  intro q _
  simpa only [CanonicalMass.atTime,extendedCanonicalMass,ENNReal.coe_lt_top,
    ite_true,ENNReal.toNNReal_coe] using hq q

end SLEExactGauge.Multipoint

end

end OAI
