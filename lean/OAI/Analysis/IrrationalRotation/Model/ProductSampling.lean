import OAI.Analysis.IrrationalRotation.Model.ProductBase
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.FiniteMeasure

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology BigOperators

namespace Invariant233.ProductModel

abbrev EndpointPair := Base × Base

def selectedEndpoint (I : Finset ℕ) (x z : Base) : Base :=
  fun i => if i ∈ I then z i else x i

def triangularEvent (I : Finset ℕ) : Set EndpointPair :=
  {xz | ∀ i ∈ I, circleRepresentative (xz.1 i) < circleRepresentative (xz.2 i)}

def triangularLaw (I : Finset ℕ) : Measure EndpointPair :=
  Measure.map (fun xz : EndpointPair => (xz.1, selectedEndpoint I xz.1 xz.2))
    ((baseMeasure.prod baseMeasure).restrict (triangularEvent I))

def triangularFirstDensity (I : Finset ℕ) (x : Base) : ℝ :=
  ∏ i ∈ I, (1 - circleRepresentative (x i))

def triangularSecondDensity (I : Finset ℕ) (y : Base) : ℝ :=
  ∏ i ∈ I, circleRepresentative (y i)

def TriangularLawProperties (I : Finset ℕ) : Prop :=
  IsFiniteMeasure (triangularLaw I) ∧
  triangularLaw I Set.univ = (1 / 2 : ℝ≥0∞) ^ I.card ∧
  (triangularLaw I).map Prod.fst =
    baseMeasure.withDensity (fun x => ENNReal.ofReal (triangularFirstDensity I x)) ∧
  (triangularLaw I).map Prod.snd =
    baseMeasure.withDensity (fun y => ENNReal.ofReal (triangularSecondDensity I y)) ∧
  (∀ᵐ xy ∂triangularLaw I, Ordered xy.1 xy.2) ∧
  (∀ x, 0 ≤ triangularFirstDensity I x ∧ triangularFirstDensity I x ≤ 1) ∧
  (∀ y, 0 ≤ triangularSecondDensity I y ∧ triangularSecondDensity I y ≤ 1)

def WeaklyConverges (η : ℕ → Measure EndpointPair) (ν : Measure EndpointPair) : Prop :=
  ∀ φ : C(EndpointPair, ℝ),
    Tendsto (fun l => ∫ xy, φ xy ∂η l) atTop (𝓝 (∫ xy, φ xy ∂ν))

def SupportedOnPositiveOrderedOrbitPairs (θ : ℕ → ℝ) (η : Measure EndpointPair) : Prop :=
  ∃ N : Finset ℕ, (∀ n ∈ N, 0 < n) ∧
    ∀ᵐ xy ∂η, Ordered xy.1 xy.2 ∧
      ∃ n ∈ N, xy.2 = rotationIterate θ (n : ℤ) xy.1

def HasUniformL2Marginals (η : ℕ → Measure EndpointPair) : Prop :=
  ∃ H : ℝ, 0 ≤ H ∧ ∀ l, ∃ f g : Lp ℝ 2 baseMeasure,
    (∀ᵐ x ∂baseMeasure, 0 ≤ f x) ∧ (∀ᵐ y ∂baseMeasure, 0 ≤ g y) ∧
    (η l).map Prod.fst = baseMeasure.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    (η l).map Prod.snd = baseMeasure.withDensity (fun y => ENNReal.ofReal (g y)) ∧
    ‖f‖ ≤ H ∧ ‖g‖ ≤ H

def OrderedOrbitSampling (θ : ℕ → ℝ) (I : Finset ℕ) : Prop :=
  ∃ η : ℕ → Measure EndpointPair,
    (∀ l, IsFiniteMeasure (η l)) ∧
    (∀ l, SupportedOnPositiveOrderedOrbitPairs θ (η l)) ∧
    HasUniformL2Marginals η ∧ WeaklyConverges η (triangularLaw I)

def HasAllFiniteCoordinateSampling (θ : ℕ → ℝ) : Prop :=
  ∀ I : Finset ℕ, OrderedOrbitSampling θ I

end Invariant233.ProductModel

end

end OAI
