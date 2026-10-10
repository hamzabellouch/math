import OAI.MeasureTheory.Falconer.Estimates.AllDimensions

namespace OAI

/-!
# The published planar incidence input

Orponen–Shmerkin–Wang, *Kaufman and Falconer estimates for radial projections
and a continuum version of Beck's theorem*, Geom. Funct. Anal. 34 (2024),
Definitions 2.5–2.6 and Theorem 2.7 (arXiv:2209.00348), following
Orponen–Shmerkin, Duke Math. J. 172 (2023), Theorem 1.3 and Remark 1.4.

The proposition below is the separated finite-set specialization in one
bounded, nonvertical line chart needed by `ang:planar-measures`. Only
`0 < b ≤ 1/2` and `b < f < 1` are retained. The chart identifies a line
with its slope and intercept. Equivalence with the published line metric
and replacement of covering counts by cardinalities cost fixed constants;
the epsilon and the small-scale threshold below are chosen after these
constants, not identified with the published theorem's original epsilon.

This is an explicit proposition to be supplied as a hypothesis. It is not
a global axiom, and no proof of this published theorem is claimed here.
-/

namespace Falconer

/-- Points and line parameters both use the Euclidean metric in this chart. -/
def FiniteSeparatedAt (δ : ℝ) (P : Finset (Space 2)) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y

/-- The normalization is by the cardinality of the entire finite set. -/
def NormalizedFiniteBallBound (δ s K : ℝ) (P : Finset (Space 2)) : Prop := by
  classical
  exact ∀ z : Space 2, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    ((P.filter (fun x => dist x z ≤ r)).card : ℝ) ≤ K * r ^ s * (P.card : ℝ)

def InBoundedLineChart (P : Finset (Space 2)) : Prop :=
  ∀ x ∈ P, |x 0| ≤ 1 ∧ |x 1| ≤ 1

/-- A point lies in the closed Euclidean δ-neighborhood of the line
with slope `l 0` and intercept `l 1`. -/
def TubeIncident (δ : ℝ) (x l : Space 2) : Prop :=
  |x 1 - l 0 * x 0 - l 1| / Real.sqrt (1 + (l 0) ^ 2) ≤ δ

/-- Exactly the range of the published planar Furstenberg estimate needed
by the higher-dimensional slicing argument, in a bounded line chart. -/
def PublishedPlanarFurstenberg : Prop := by
  classical
  exact ∀ b f : ℝ, 0 < b → b ≤ 1 / 2 → b < f → f < 1 →
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
      FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ f (δ ^ (-ε)) P →
    ∀ T : Space 2 → Finset (Space 2),
      (∀ x ∈ P, (T x).Nonempty ∧ InBoundedLineChart (T x) ∧
        FiniteSeparatedAt δ (T x) ∧ NormalizedFiniteBallBound δ b (δ ^ (-ε)) (T x) ∧
        ∀ l ∈ T x, TubeIncident δ x l) →
      δ ^ (-2 * b - ε) ≤ ((P.biUnion T).card : ℝ)

end Falconer

end OAI
