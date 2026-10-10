import OAI.MeasureTheory.Falconer.Radial.RadialMoments
import OAI.MeasureTheory.Falconer.Angular.SphereCapBound
import OAI.MeasureTheory.Falconer.Geometry.EuclideanRieszEnergy

namespace OAI

/-! # The exact all-dimensional published radial moment input

T. Orponen, *On the dimension and smoothness of radial projections*,
Analysis & PDE 12 (2019), 1273–1294, proof of Theorem 1.13,
equations (3.5)–(3.6), printed pp. 1290–1292.
https://msp.org/apde/2019/12-5/apde-v12-n5-p06-s.pdf

Only s=h+delta/2, t=h-delta/4, p=1+delta/(8h) in dimension h+1 are used.
The strict parameter inequalities are proved locally. On disjoint compact
supports the source weight |x-y|^(-h) and its inverse are uniformly bounded,
so the published moment yields this unweighted finite moment and absolute
continuity. The reference measure is the actual Euclidean surface measure.
The moment bound concerns the radial projection and its absolute continuity.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

def PublishedRadialMoment : Prop :=
  ∀ h : ℕ, 1 ≤ h → ∀ (μ ν : ProbabilityMeasure (Space (h+1))) (δ : ℝ),
    0 < δ → δ < 1 →
    IsCompact (μ : Measure (Space (h+1))).support →
    IsCompact (ν : Measure (Space (h+1))).support →
    Disjoint (μ : Measure (Space (h+1))).support (ν : Measure (Space (h+1))).support →
    PlanarFalconer.rieszEnergyOn (μ : Measure (Space (h+1))) ((h:ℝ)+δ/2) < ∞ →
    PlanarFalconer.rieszEnergyOn (ν : Measure (Space (h+1))) ((h:ℝ)-δ/4) < ∞ →
    (∀ᵐ x ∂(ν : Measure (Space (h+1))),
      (μ : Measure (Space (h+1))).map (radialDirection x) ≪ surfaceMeasure (h+1)) ∧
    (∫⁻ x, ∫⁻ w,
      ((μ : Measure (Space (h+1))).map (radialDirection x)).rnDeriv (surfaceMeasure (h+1)) w ^
        (1+δ/(8*(h:ℝ))) ∂surfaceMeasure (h+1) ∂(ν : Measure (Space (h+1)))) < ∞

end Falconer

end OAI
