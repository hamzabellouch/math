import Mathlib

namespace OAI

noncomputable section

open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal

abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Plane) x)]

def coordinateMetric (x : M) (y : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => inner ℝ
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (chartAt Plane x).symm y
      (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (chartAt Plane x).symm y
      (EuclideanSpace.single j 1))

def coordinateDensity (x : M) (y : Plane) : ℝ :=
  Real.sqrt (coordinateMetric x y).det

def coordPartial (f : Plane → ℝ) (i : Fin 2) (y : Plane) : ℝ :=
  fderiv ℝ f y (EuclideanSpace.single i 1)

def laplaceBeltrami (u : M → ℝ) (x : M) : ℝ :=
  (coordinateDensity x (chartAt Plane x x))⁻¹ *
    ∑ i : Fin 2, coordPartial (fun y => coordinateDensity x y *
      ∑ j : Fin 2, ((coordinateMetric x y)⁻¹ i j) *
        coordPartial (u ∘ (chartAt Plane x).symm) j y) i (chartAt Plane x x)

def nodalSet (u : M → ℝ) : Set M := {x | u x = 0}

def nodalLength (u : M → ℝ) : ℝ≥0∞ :=
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  Measure.hausdorffMeasure 1 (nodalSet u)

def MainStatement (M : Type*) [MetricSpace M] [ChartedSpace Plane M]
    [IsManifold 𝓘(ℝ, Plane) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Plane) x)] : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ), 0 < lam → ∀ (u : M → ℝ),
    ContMDiff 𝓘(ℝ, Plane) 𝓘(ℝ) ∞ u → u ≠ 0 →
    (∀ x, -laplaceBeltrami u x = lam * u x) →
    nodalLength u ≤ ENNReal.ofReal (C * Real.sqrt lam)

theorem Main [CompactSpace M] [ConnectedSpace M]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane
      (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]
    [IsRiemannianManifold 𝓘(ℝ,Plane) M] : MainStatement M := by
  sorry

end SharpNodal

end

end OAI
