import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.DistanceSquare

namespace OAI

noncomputable section
namespace YauCounterexamples
open Set Filter Metric Manifold
open scoped Topology ContDiff RealInnerProductSpace Matrix.Norms.Elementwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma coefficientElliptic_flux {ι : Type*} [Fintype ι] (e : ι → E)
    (a : ι → ι → SmoothScalar E) (u : SmoothScalar E) (x : E) :
    coefficientElliptic e a u x = ∑ i, fderiv ℝ
      (fun y => ∑ j, a i j y * SmoothScalar.directional (e j) u y) x (e i) := by
  have he : coefficientElliptic e a u =
      ∑ i, SmoothScalar.directional (e i) (∑ j, a i j * SmoothScalar.directional (e j) u) := by
    simp only [coefficientElliptic, map_sum]
  rw [he, SmoothScalar.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change fderiv ℝ _ x (e i) = _
  congr 2
  funext y
  simp only [SmoothScalar.sum_apply, Subalgebra.coe_mul, Pi.mul_apply]

end YauCounterexamples


end

end OAI
