import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OAI.Geometry.NodalSets.Charts.ChartHessianLemmas

namespace OAI

namespace Yau.Geometry
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma positive_metric_injective (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) : Function.Injective g := by
  intro u v huv
  apply sub_eq_zero.mp
  by_contra h
  have hz : g (u-v) = 0 := by rw [map_sub, huv, sub_self]
  have hh := hp (u-v) h
  rw [hz, zero_apply] at hh
  exact (lt_irrefl 0 hh)

variable [FiniteDimensional ℝ E]

lemma dual_continuous_finrank : Module.finrank ℝ (E →L[ℝ] ℝ) = Module.finrank ℝ E := by
  rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).finrank_eq]
  exact Subspace.dual_finrank_eq

def positiveMetricEquiv (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) : E ≃L[ℝ] E →L[ℝ] ℝ :=
  (g.toLinearMap.linearEquivOfInjective (positive_metric_injective g hp)
    dual_continuous_finrank.symm).toContinuousLinearEquiv

lemma positiveMetricEquiv_apply (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) (u v : E) :
    positiveMetricEquiv g hp u v = g u v := rfl

theorem positive_metric_connection (g : E →L[ℝ] E →L[ℝ] ℝ)
    (hp : ∀ v : E, v ≠ 0 → 0 < g v v) (hs : ∀ u v, g u v = g v u)
    (D : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (hD : ∀ w u v, D w u v = D w v u) :
    ∃ B : E →L[ℝ] E →L[ℝ] E, (∀ u v, B u v = B v u) ∧
      ∀ w u v, D w u v = g (B w u) v + g u (B w v) := by
  let m := positiveMetricEquiv g hp
  refine ⟨christoffelTensor m D, christoffelTensor_symmetric m D hD, ?_⟩
  exact christoffelTensor_cancel m hs D hD

end
end Yau.Geometry

end OAI
