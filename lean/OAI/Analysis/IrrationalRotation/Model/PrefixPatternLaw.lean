import OAI.Analysis.IrrationalRotation.Model.ProductSampling

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel.PrefixPatterns

def replacement (I : Finset ℕ) (xz : EndpointPair) : EndpointPair :=
  (xz.1, selectedEndpoint I xz.1 xz.2)

def rectangleDensity (U V : Set Circle) : Circle × Circle → ℝ≥0∞ :=
  (U ×ˢ V).indicator (fun _ => (circleMeasure U * circleMeasure V)⁻¹)

def patternDensity (I : Finset ℕ) (g : Base → ℝ≥0∞)
    (U V : ℕ → Set Circle) (xz : EndpointPair) : ℝ≥0∞ :=
  g xz.1 * ∏ i ∈ I, rectangleDensity (U i) (V i) (xz.1 i, xz.2 i)

def patternLaw (I : Finset ℕ) (g : Base → ℝ≥0∞)
    (U V : ℕ → Set Circle) : Measure EndpointPair :=
  ((baseMeasure.prod baseMeasure).withDensity (patternDensity I g U V)).map
    (replacement I)

def mixtureLaw {C : Type*} [Fintype C] (w : C → ℝ≥0∞)
    (I : C → Finset ℕ) (g : C → Base → ℝ≥0∞)
    (U V : C → ℕ → Set Circle) : Measure EndpointPair :=
  ∑ c, w c • patternLaw (I c) (g c) (U c) (V c)

end Invariant233.ProductModel.PrefixPatterns

end

end OAI
