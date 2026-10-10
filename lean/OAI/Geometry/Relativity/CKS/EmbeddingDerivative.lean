import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.LocalConstraints
import OAI.Geometry.Relativity.CKS.VolumeDefinitions

namespace OAI

noncomputable section
open Set Manifold Bundle Filter Function
open scoped ContDiff Topology
namespace CKSEmbeddingDerivative
attribute [local instance] halfSpaceDimension_neZero

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

omit [IsManifold I ∞ M] in
lemma extended_chart_derivative_injective [IsManifold I ∞ M] (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {x : M} (hx : x ∈ e.source) :
    Injective (mfderiv I 𝓘(ℝ,E) (e.extend I) x) := by
  have hed : e.MDifferentiable I I := ⟨
    (contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have hcomp := mfderiv_comp x I.mdifferentiableAt ((hed.1 x hx).mdifferentiableAt (e.open_source.mem_nhds hx))
  change mfderiv I 𝓘(ℝ,E) (e.extend I) x = _ at hcomp
  rw [I.hasMFDerivAt.mfderiv] at hcomp
  change mfderiv I 𝓘(ℝ,E) (e.extend I) x = mfderiv I I e x at hcomp
  rw [hcomp]
  exact hed.mfderiv_injective hx

omit [IsManifold I ∞ N] in
lemma immersion_derivative_injective [IsManifold I ∞ N] {f : M → N} {x : M}
    (h : IsImmersionAt I I ∞ f x) : Injective (mfderiv I I f x) := by
  let A : E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E h.complement).comp
    h.equiv.symm.toContinuousLinearMap
  let L : N → E := A ∘ (h.codChart.extend I)
  have hL : ContMDiffAt I 𝓘(ℝ,E) ∞ L (f x) :=
    A.contMDiff.contMDiffAt.comp _
      (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas h.mem_codChart_source)
  have heq : (L ∘ f) =ᶠ[𝓝 x] h.domChart.extend I := by
    filter_upwards [h.domChart.open_source.mem_nhds h.mem_domChart_source] with y hy
    have hy' : y ∈ (h.domChart.extend I).source := by simpa only [OpenPartialHomeomorph.extend_source] using hy
    have hw := h.writtenInCharts ((h.domChart.extend I).map_source hy')
    dsimp only [Function.comp_apply] at hw
    rw [(h.domChart.extend I).left_inv hy'] at hw
    change A ((h.codChart.extend I) (f y)) = _
    rw [hw]
    simp only [A,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply ]
    rfl
  have hdL := hL.mdifferentiableAt (by simp)
  have hdf := h.contMDiffAt.mdifferentiableAt (by simp)
  have hder := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ,E))
  rw [mfderiv_comp x hdL hdf] at hder
  change _ = mfderiv I 𝓘(ℝ,E) (h.domChart.extend I) x at hder
  have hinj := extended_chart_derivative_injective h.domChart h.domChart_mem_maximalAtlas
    h.mem_domChart_source
  rw [← hder] at hinj
  have hi' : Injective ((mfderiv I 𝓘(ℝ,E) L (f x)) ∘ (mfderiv I I f x)) := hinj
  exact hi'.of_comp

lemma smooth_embedding_derivative_injective {f : M → N} (h : IsSmoothEmbedding I I ∞ f) :
    ∀ x, Injective (mfderiv I I f x) := fun x =>
  immersion_derivative_injective (h.isImmersion.isImmersionAt x)

end CKSEmbeddingDerivative

end

end OAI
