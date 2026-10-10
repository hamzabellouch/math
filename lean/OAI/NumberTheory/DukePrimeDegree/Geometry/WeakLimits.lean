import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-!
# Passing packet estimates to weak limits

The ordinary-ball estimate in paper 031-01 is proved for each fixed ball,
with a packet threshold that may depend on that ball. Portmanteau passes
this estimate to the limit without a uniform threshold or an exchange of
shrinking-radius and packet limits. Continuous diagonal transformations
also preserve invariance in the weak limit.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

variable {X I : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] [HasOuterApproxClosed X]
    {L : Filter I} [NeBot L]

/-- Any eventual upper bound on the mass of a fixed open set passes to a
weak probability limit. -/
theorem open_mass_le_of_tendsto
    (μs : I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs L (𝓝 μ)) (U : Set X) (hU : IsOpen U)
    (C : ℝ≥0∞) (hbound : ∀ᶠ i in L, (μs i : Measure X) U ≤ C) :
    (μ : Measure X) U ≤ C := by
  calc
    (μ : Measure X) U ≤ liminf (fun i => (μs i : Measure X) U) L :=
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hU
    _ ≤ C := liminf_le_of_frequently_le' hbound.frequently

/-- The radius and center dependent thresholds in the manuscript's vector
box estimate suffice for a uniform ordinary-ball bound on the limit. -/
theorem ball_bounds_of_tendsto
    (μs : I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs L (𝓝 μ)) (balls : X → ℝ → Set X)
    (hopen : ∀ x r, IsOpen (balls x r)) (n : ℕ)
    (hbound : ∀ K : Set X, IsCompact K →
      ∃ C r₀ : ℝ, 0 ≤ C ∧ 0 < r₀ ∧
        ∀ x ∈ K, ∀ r, 0 < r → r < r₀ →
          ∀ᶠ i in L, (μs i : Measure X) (balls x r) ≤ ENNReal.ofReal (C * r ^ n)) :
    ∀ K : Set X, IsCompact K →
      ∃ C r₀ : ℝ, 0 ≤ C ∧ 0 < r₀ ∧
        ∀ x ∈ K, ∀ r, 0 < r → r < r₀ →
          (μ : Measure X) (balls x r) ≤ ENNReal.ofReal (C * r ^ n) := by
  intro K hK
  obtain ⟨C, r₀, hC, hr₀, hbounds⟩ := hbound K hK
  refine ⟨C, r₀, hC, hr₀, ?_⟩
  intro x hx r hr hrr₀
  exact open_mass_le_of_tendsto μs μ hlim (balls x r) (hopen x r)
    (ENNReal.ofReal (C * r ^ n)) (hbounds x hx r hr hrr₀)

/-- Push-forward invariance under a continuous transformation survives
weak convergence. Eventual invariance is enough. -/
theorem invariant_of_tendsto
    (μs : I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs L (𝓝 μ)) (T : X → X) (hT : Continuous T)
    (hinv : ∀ᶠ i in L, (μs i).map T = μs i) :
    μ.map T = μ := by
  have hmapped : Tendsto (fun i => (μs i).map T) L (𝓝 (μ.map T)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hlim hT
  have hsame : Tendsto (fun i => (μs i).map T) L (𝓝 μ) :=
    hlim.congr' (hinv.mono fun _ hi => hi.symm)
  exact tendsto_nhds_unique hmapped hsame

/-- Weak limits of invariant probabilities remain invariant as measures. -/
theorem measure_invariant_of_tendsto
    (μs : I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto μs L (𝓝 μ)) (T : X → X) (hT : Continuous T)
    (hinv : ∀ᶠ i in L, Measure.map T (μs i : Measure X) = (μs i : Measure X)) :
    Measure.map T (μ : Measure X) = (μ : Measure X) := by
  have hinv' : ∀ᶠ i in L, (μs i).map T = μs i := by
    filter_upwards [hinv] with i hi
    exact Subtype.ext hi
  exact congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X))
    (invariant_of_tendsto μs μ hlim T hT hinv')

end DukePrimeDegree

end OAI
