import OAI.Probability.SLE.Mass.CanonicalRawMass
import OAI.Probability.SLE.Mass.TerminalMassTestLimit

namespace OAI

/-! Terminal extension of the fixed raw canonical mass functional. Its
integer-time vague limit agrees with the locally exhausted terminal mass. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : MeasurableSpace C(ℝ≥0,ℝ) := borel _
local instance : BorelSpace C(ℝ≥0,ℝ) := ⟨rfl⟩
local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

structure RawCanonicalMass where
  process : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane
  terminal : C(ℝ≥0,ℝ) → Measure upperHalfPlane
  progressive : IsProgressive driverPathFiltration process
  radon : ∀ t p, (process t p).Regular ∧ IsFiniteMeasureOnCompacts (process t p)
  terminal_measurable : Measurable terminal
  terminal_radon : ∀ p, (terminal p).Regular ∧ IsFiniteMeasureOnCompacts (terminal p)
  nonanticipating : ∀ t p q, (∀ s ≤ t, p s=q s) → process t p=process t q

def rawTerminalMass (R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane)
    (p : C(ℝ≥0,ℝ)) : Measure upperHalfPlane :=
  canonicalRadonLimit (fun n : ℕ => R n p)

lemma rawTerminalMass_measurable
    (R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane)
    (hRp : IsProgressive driverPathFiltration R)
    (hRr : ∀ t p, (R t p).Regular ∧ IsFiniteMeasureOnCompacts (R t p)) :
    Measurable (rawTerminalMass R) := by
  apply canonicalRadonLimit_measurable (fun n : ℕ => R n)
    (fun n p => (hRr n p).2)
  intro n f
  exact measurable_halfPlane_compact_test_integral (R n)
    (hRp.adapted.measurable (i := (n:ℝ≥0))) (fun p => (hRr n p).1) f

lemma rawTerminalMass_radon
    (R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane) (p : C(ℝ≥0,ℝ)) :
    (rawTerminalMass R p).Regular ∧ IsFiniteMeasureOnCompacts (rawTerminalMass R p) := by
  have : (rawTerminalMass R p).Regular := canonicalRadonLimit_regular _
  exact ⟨this,inferInstance⟩

theorem CanonicalMass.rawTerminal_realizes
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (R : ℝ≥0 → C(ℝ≥0,ℝ) → Measure upperHalfPlane)
    (he : ∀ᵐ ω ∂P, ∀ t, R t (sourceDriverPath B hBc ω) = C.process t ω) :
    ∀ᵐ ω ∂P, rawTerminalMass R (sourceDriverPath B hBc ω) = C.rational.terminal ω := by
  filter_upwards [he,C.paths,C.exhaustion] with ω he hp hlim
  apply canonicalRadonLimit_identified _ _
  refine ⟨(C.rational.terminal_radon ω).1,?_⟩
  intro f
  let : (C.rational.terminal ω).Regular := (C.rational.terminal_radon ω).1
  have ht := terminal_mass_test_tendsto (C.rational.terminal ω) (fun t => C.process t ω)
    (fun t => (C.radon t ω).1) hp.dominated hlim f
  simpa only [Function.comp_def,he] using ht.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))

theorem CanonicalMass.exists_raw_canonical
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : CanonicalMass P κ B hBm γ G)
    (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    ∃ R : RawCanonicalMass, ∀ᵐ ω ∂P,
      (∀ t, R.process t (sourceDriverPath B hBc ω) = C.process t ω) ∧
        R.terminal (sourceDriverPath B hBc ω) = C.rational.terminal ω := by
  obtain ⟨R,hRp,hRr,hRn,he⟩ := C.exists_raw_nonanticipating_functional hBc
  refine ⟨⟨R,rawTerminalMass R,hRp,hRr,rawTerminalMass_measurable R hRp hRr,
    rawTerminalMass_radon R,hRn⟩,?_⟩
  filter_upwards [he,C.rawTerminal_realizes hBc R he] with ω hf ht
  exact ⟨hf,ht⟩

end SLEExactGauge.Multipoint

end

end OAI
