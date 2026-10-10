import Mathlib

namespace OAI

namespace Yau
namespace Target
open Bundle Manifold Matrix Filter
open scoped ContDiff Topology ENNReal
noncomputable section

abbrev Base := Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1

abbrev Manifold5 := Base × Circle

abbrev Model := EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 1)

abbrev modelWithCorners := (𝓡 4).prod (𝓡 1)

abbrev SmoothMetric := ContMDiffRiemannianMetric modelWithCorners ∞ Model
  (fun x : Manifold5 ↦ TangentSpace modelWithCorners x)

abbrev Index := Fin (Module.finrank ℝ Model)

def frame : Module.Basis Index ℝ Model := Module.finBasis ℝ Model

def metricMatrix (g : SmoothMetric) (c : PartialEquiv Manifold5 Model)
    (y : Model) : Matrix Index Index ℝ := fun i j ↦
  g.inner (c.symm y)
    (mfderiv 𝓘(ℝ, Model) modelWithCorners c.symm y (frame i))
    (mfderiv 𝓘(ℝ, Model) modelWithCorners c.symm y (frame j))

def volumeFactor (g : SmoothMetric) (c : PartialEquiv Manifold5 Model)
    (y : Model) : ℝ := Real.sqrt (metricMatrix g c y).det

def chartLaplacian (g : SmoothMetric) (c : PartialEquiv Manifold5 Model)
    (u : Manifold5 → ℝ) (y : Model) : ℝ :=
  (volumeFactor g c y)⁻¹ * ∑ i, fderiv ℝ
    (fun z ↦ volumeFactor g c z * ∑ j,
      (metricMatrix g c z)⁻¹ i j * fderiv ℝ (u ∘ c.symm) z (frame j)) y (frame i)

def nodalMeasure (g : SmoothMetric) (u : Manifold5 → ℝ) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle modelWithCorners ∞ Model
      (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) := inferInstance
  letI : MeasurableSpace Manifold5 := borel Manifold5
  letI : BorelSpace Manifold5 := ⟨rfl⟩
  letI : IsContinuousRiemannianBundle Model
      (fun x : Manifold5 ↦ TangentSpace modelWithCorners x) :=
    ⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩
  letI : EMetricSpace Manifold5 := EMetricSpace.ofRiemannianMetric modelWithCorners Manifold5
  MeasureTheory.Measure.hausdorffMeasure (4 : ℝ) {x | u x = 0}

def MainTarget : Prop :=
  ∃ (g : SmoothMetric) (lam : ℕ → ℝ) (u : ℕ → Manifold5 → ℝ),
    (∀ k, 0 < lam k) ∧
    (∀ k, u k ≠ 0) ∧
    (∀ k, ContMDiff modelWithCorners 𝓘(ℝ, ℝ) ∞ (u k)) ∧
    (∀ k x, -chartLaplacian g (extChartAt modelWithCorners x) (u k) ((extChartAt modelWithCorners x) x) =
      lam k * u k x) ∧
    Tendsto lam atTop atTop ∧
    Tendsto (fun k ↦ nodalMeasure g (u k) / ENNReal.ofReal (Real.sqrt (lam k)))
      atTop (𝓝 ⊤)

theorem yau_nodal_set_upper_bound_counterexample : MainTarget := by
  sorry

end
end Target
end Yau

end OAI
