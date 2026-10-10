import OAI.Analysis.IrrationalRotation.Model.BlockedProductCoupling
import OAI.Analysis.IrrationalRotation.Model.ProductScales
import OAI.Analysis.IrrationalRotation.Model.ProductCocycle
import OAI.Analysis.IrrationalRotation.Model.SourceCouplingMarginals

namespace OAI

noncomputable section
open scoped ComplexConjugate

namespace Invariant233.BlockedProductCoupling

def sourceBasisZero : ProductModel.Fiber := lp.single 2 (0 : ℤ) (1 : ℂ)

abbrev ProjectionField := ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber

def projectionDiagonal (P : ProjectionField) (x : ProductModel.Base) : ℝ :=
  ((P x sourceBasisZero) 0).re

def sourceRetainedEvent {X : Type*} (m : ℕ → ℕ) (K : ℕ → ℝ)
    (r : X → ℝ) (x y : Sample m → X) (j : ℕ) : Set (Sample m) :=
  currentEvent m j \ (futureBad m K j ∪
    ({z | r (x z) < 1 / ((j + 1 : ℕ) : ℝ)} ∪
      {z | 1 - r (y z) < 1 / ((j + 1 : ℕ) : ℝ)}))

noncomputable def sourceLaw (p : ProductScaleData) (j : ℕ) : MeasureTheory.Measure (Sample p.m) :=
  law p.m ProductScaleData.kappa (fun s _ => p.a s) (fun s _ => p.b s) j

def sourceEvent (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (r : ProductModel.Base → ℝ) (j : ℕ) : Set (Sample p.m) :=
  sourceRetainedEvent p.m (fun s => (p.K s : ℝ)) r
    (circleLeftEndpoint e) (circleRightEndpoint e) j

def unflatten {m : ℕ → ℕ} (e : ℕ ≃ Σ s, Fin (m s))
    (ω : OrderedProductCoupling.Sample) : Sample m :=
  fun s i => ω (e.symm ⟨s, i⟩)

def flatSourceEvent (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (r : ProductModel.Base → ℝ) (j : ℕ) : Set OrderedProductCoupling.Sample :=
  unflatten e ⁻¹' sourceEvent p e r j

def sourceCoefficientA (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (θ : ℕ → ℝ) (P : ProjectionField) (z : Sample p.m) (v : ℤ) : ℂ :=
  (P (circleLeftEndpoint e z) sourceBasisZero) v /
    (ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) v
      (circleLeftEndpoint e z) : ℂ)

def sourceCoefficientB (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (θ : ℕ → ℝ) (P : ProjectionField) (z : Sample p.m) (v : ℤ) : ℂ :=
  (ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) (-v)
    (circleRightEndpoint e z) : ℂ) *
      conj (((1 - P (circleRightEndpoint e z)) sourceBasisZero) (-v))

end Invariant233.BlockedProductCoupling

end

end OAI
