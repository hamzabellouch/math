import OAI.MeasureTheory.DyadicAvoidance.CenterRouteExposure
import OAI.MeasureTheory.DyadicAvoidance.ExposureUnionBound
import OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310.CenterFailureBound

open FiniteTableModel CenterRouteExposure

/-- The actual full-outcome fiber of the center selector exposure. -/
def centerAtom {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (x : ℝ) (ξ : Node M d × Fin M → Bool) :
    Set (SelectorTable bS × TerminalTable bT) :=
  {ω | centerExposure bS x ω.1 = ξ}

/-- No default occurs on the actual center path. Terminal coordinates do not
enter this event, but are retained in the probability space. -/
def noDefaultEvent {M d : ℕ} (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (x : ℝ) : Set (SelectorTable bS × TerminalTable bT) :=
  {ω | ∀ k < d, centerChoice bS x
    (RoutingPath.routeFrom (centerChoice bS x) k [] ω.1) ω.1 ≠ Fin.last M}

/-- Concrete assembly of the atom bounds into the raw `2p` failure estimate.
All exposure fibers, their measurability, and their total mass are discharged
here for the canonical finite selector/terminal table model. -/
theorem raw_failure_le_of_center_atoms {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (μ : Measure (SelectorTable bS × TerminalTable bT)) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 ≤ p) (B : SelectorTable bS × TerminalTable bT → Set ℝ)
    (N : Set ℕ) (x : ℝ)
    (hbad : μ (noDefaultEvent bS bT x) ≤ ENNReal.ofReal p)
    (hatom : ∀ ξ : Node M d × Fin M → Bool, GoodExposure bS x ξ →
      μ ({ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ∩
          centerAtom bS bT x ξ) ≤
        ENNReal.ofReal p * μ (centerAtom bS bT x ξ)) :
    μ {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} ≤
      ENNReal.ofReal (2 * p) := by
  classical
  let f : SelectorTable bS × TerminalTable bT → (Node M d × Fin M → Bool) :=
    fun ω => centerExposure bS x ω.1
  let good : Set (Node M d × Fin M → Bool) := {ξ | GoodExposure bS x ξ}
  have hf (ξ) : MeasurableSet {ω | f ω = ξ} := (Set.to_countable _).measurableSet
  have hbad' : μ {ω | f ω ∉ good} ≤ ENNReal.ofReal p := by
    have heq : {ω | f ω ∉ good} = noDefaultEvent bS bT x := by
      ext ω
      exact badExposure_centerExposure_iff bS x ω.1
    rwa [heq]
  have h := ExposureUnionBound.measure_le_of_finite_exposure μ f hf
    {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)} good
    (ENNReal.ofReal p) (ENNReal.ofReal p) hbad' (fun ξ hξ => hatom ξ hξ)
  calc
    μ {ω | x ∈ Auxiliary.exceptionalCenters (B ω) N (fun n => (2 : ℝ)⁻¹ ^ n)}
        ≤ ENNReal.ofReal p + ENNReal.ofReal p := h
    _ = ENNReal.ofReal (2 * p) := by
      rw [← ENNReal.ofReal_add hp hp]
      congr 1
      ring

end Problem310.CenterFailureBound

end

end OAI
