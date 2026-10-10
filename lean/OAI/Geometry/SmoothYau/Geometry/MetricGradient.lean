import Mathlib
import OAI.Geometry.SmoothYau.Model

namespace OAI





noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

def metricGradient (g : SmoothMetric E M) (u : M → ℝ) (x : M) :
    TangentSpace 𝓘(ℝ,E) x := by
  letI : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
    show FiniteDimensional ℝ E from inferInstance
  exact (InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,E) x)).symm
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x)

lemma metricGradient_pairing (g : SmoothMetric E M) (u : M → ℝ) (x : M)
    (v : TangentSpace 𝓘(ℝ,E) x) :
    g.inner x (metricGradient g u x) v = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ,E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,E) x) :=
    show FiniteDimensional ℝ E from inferInstance
  exact congrArg (fun L : TangentSpace 𝓘(ℝ,E) x →L[ℝ] ℝ => L v)
    ((InnerProductSpace.toDual ℝ (TangentSpace 𝓘(ℝ,E) x)).apply_symm_apply _)

omit [FiniteDimensional ℝ E] in
private lemma positive_bilinear_unique (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ z : E, z ≠ 0 → 0 < B z z) (v w : E)
    (h : ∀ z, B v z = B w z) : v = w := by
  by_contra hn
  have hp := hB (v - w) (sub_ne_zero.mpr hn)
  have hz : B (v - w) (v - w) = 0 := by
    rw [map_sub B v w, sub_apply, h, sub_self]
  linarith

lemma metricGradient_unique (g : SmoothMetric E M) (u : M → ℝ) (x : M)
    (v : TangentSpace 𝓘(ℝ,E) x)
    (hv : ∀ w, g.inner x v w = mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) u x w) :
    v = metricGradient g u x := by
  apply positive_bilinear_unique (E := E) (g.inner x) (g.pos x) v (metricGradient g u x)
  intro w
  exact (hv w).trans (metricGradient_pairing g u x w).symm

end YauCounterexamples

end

end OAI
