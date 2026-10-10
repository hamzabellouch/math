import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

noncomputable def diagonal (μ : Measure X) : Measure (X × X) :=
  μ.map (fun x => (x, x))

noncomputable def mixture (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) : Measure (X × X) :=
  q • diagonal μ + ∑ i, p i • (u i).prod (v i)

noncomputable def intervalLaw (a b : ℝ) : Measure ℝ :=
  volume[|Ico a b]

noncomputable def labelledMixture [MeasurableSpace (Option I)] (μ : Measure X)
    (q : ℝ≥0∞) (p : I → ℝ≥0∞) (u v : I → Measure X) :
    Measure (Option I × (X × X)) :=
  q • (diagonal μ).map (fun z => (none, z)) +
    ∑ i, p i • ((u i).prod (v i)).map (fun z => (some i, z))

end Invariant233.CouplingMixture

end OAI
