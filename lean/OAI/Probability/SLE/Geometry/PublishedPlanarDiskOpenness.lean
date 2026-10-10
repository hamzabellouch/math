import Mathlib

namespace OAI

/-! The planar-disk specialization of invariance of domain used for an
embedded ribbon coordinate patch. This is an explicit published parameter,
not a new axiom. Reference: A. Hatcher, Algebraic Topology (Cambridge, 2002),
Theorem 2B.3, p. 172, specialized to n=2 and an open Euclidean disk.
https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf -/

noncomputable section
open Set Metric

namespace SLEExactGauge

def PublishedPlanarDiskOpenness : Prop :=
  ∀ (P : ℂ → ℂ) (x : ℂ) (r : ℝ), 0 < r →
    ContinuousOn P (ball x r) → InjOn P (ball x r) → IsOpen (P '' ball x r)

end SLEExactGauge

end

end OAI
