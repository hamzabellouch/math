import Mathlib

namespace OAI

namespace WeakMTWGlobalSupport

section

open Bundle Manifold Set
open scoped Bundle Manifold ContDiff Topology
namespace ChartMetric
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

abbrev chartLift (x : M) (y : E) : E →L[ℝ] TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y) :=
  (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ ((chartAt E x).symm y)

def metric (x : M) (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ (E := TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))).bilinearComp
    (chartLift x y) (chartLift x y)

@[simp] theorem metric_apply (x : M) (y v w : E) :
    metric x y v w = inner ℝ (chartLift x y v) (chartLift x y w) := rfl

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)] in
theorem lift_smooth (x : M) (v : E) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨(chartAt E x).symm y, chartLift x y v⟩ : TangentBundle 𝓘(ℝ, E) M))
      (chartAt E x).target := by
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : ∀ y ∈ (chartAt E x).target, (chartAt E x).symm y ∈ e.baseSet := by
    intro y hy
    rw [TangentBundle.trivializationAt_baseSet]
    exact (chartAt E x).map_target hy
  have hc := e.contMDiffOn_symm (IB := 𝓘(ℝ, E)) (n := ∞)
  have hf : ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun y => ((chartAt E x).symm y, v)) (chartAt E x).target :=
    contMDiffOn_chart_symm.prodMk contMDiffOn_const
  have hcomp := hc.comp hf (fun y hy => e.mem_target.mpr (hb y hy))
  apply hcomp.congr
  intro y hy
  change (⟨(chartAt E x).symm y, e.symmL ℝ ((chartAt E x).symm y) v⟩ : TangentBundle 𝓘(ℝ, E) M) =
    e.toOpenPartialHomeomorph.symm ((chartAt E x).symm y, v)
  rw [e.symmL_apply (hb y hy), e.mk_symm (hb y hy)]

theorem metric_smooth [FiniteDimensional ℝ E]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
    (x : M) : ContDiffOn ℝ ∞ (metric x) (chartAt E x).target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  apply contMDiffOn_iff_contDiffOn.mp
  exact @ContMDiffOn.inner_bundle E _ _ E _ 𝓘(ℝ, E) ∞ M _ _ E _ _
    (fun x : M => TangentSpace 𝓘(ℝ, E) x) _
    (fun x : M => (inferInstance : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x)))
    (fun x : M => (inferInstance : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) x)))
    _ _ E _ _ E _ 𝓘(ℝ, E) E _ _ _ (fun y => (chartAt E x).symm y)
    (fun y => chartLift x y v) (fun y => chartLift x y w) _ (lift_smooth x v) (lift_smooth x w)

theorem metric_symmetric (x : M) (y v w : E) : metric x y v w = metric x y w v := by
  rw [metric_apply, metric_apply]
  exact @real_inner_comm (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))
    (inferInstance : SeminormedAddCommGroup (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y)))
    (inferInstance : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))) _ _

theorem metric_positive (x : M) {y : E} (hy : y ∈ (chartAt E x).target)
    {v : E} (hv : v ≠ 0) : 0 < metric x y v v := by
  rw [metric_apply]
  apply (@real_inner_self_pos (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))
    (inferInstance : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y)))
    (inferInstance : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E) ((chartAt E x).symm y))) _).mpr
  intro he
  let e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) x
  have hb : (chartAt E x).symm y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact (chartAt E x).map_target hy
  apply hv
  have hh := congrArg (e.continuousLinearMapAt ℝ ((chartAt E x).symm y)) he
  change e.continuousLinearMapAt ℝ ((chartAt E x).symm y) (e.symmL ℝ ((chartAt E x).symm y) v) =
    e.continuousLinearMapAt ℝ ((chartAt E x).symm y) 0 at hh
  simpa only [e.continuousLinearMapAt_symmL hb, map_zero] using hh

end
end ChartMetric
end

end WeakMTWGlobalSupport

end OAI
