import OAI.Geometry.Relativity.CKS.SurfaceVolume

namespace OAI

noncomputable section
open Set Filter Manifold Function
open scoped ContDiff Topology
namespace CKSEmbeddingDerivative
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

lemma image_interior_mem_nhds {f : M → N} (hf : IsSmoothEmbedding I I ∞ f)
    {x : M} (hx : x ∈ I.interior M) : f '' I.interior M ∈ 𝓝 (f x) := by
  have hmd := (hf.isImmersion.contMDiff x).mdifferentiableAt (by simp)
  let A : E →L[ℝ] E := mfderiv I I f x
  have hA : Injective A := smooth_embedding_derivative_injective hf x
  have hb : Bijective (mfderiv I I f x) :=
    ⟨hA, (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mp hA⟩
  let F := writtenInExtChartAt I I x f
  let z := extChartAt I x x
  have hrange : range I ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hx
  have hF : ContDiffAt ℝ ∞ F z :=
    (contMDiffAt_iff.mp (hf.isImmersion.contMDiff x)).2.contDiffAt hrange
  have hbF : Bijective (fderiv ℝ F z) := by
    simp only [mfderiv,hmd,ite_true] at hb
    rwa [fderivWithin_eq_fderiv (I.uniqueDiffOn _ (mem_of_mem_nhds hrange))
      (hF.differentiableAt (by simp))] at hb
  let L : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F z).toLinearMap hbF).toContinuousLinearEquiv
  have hL : L.toContinuousLinearMap = fderiv ℝ F z := by ext v; rfl
  have hd : HasFDerivAt F (L : E →L[ℝ] E) z := by
    rw [hL]
    exact (hF.differentiableAt (by simp)).hasFDerivAt
  let e := hF.toOpenPartialHomeomorph F hd (by simp)
  have he : z ∈ e.source := hF.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hi : I.interior M ∈ 𝓝 x := (I.isOpen_interior (by simp : (∞ : ℕ∞ω) ≠ 0)).mem_nhds hx
  have hs : f ⁻¹' (extChartAt I (f x)).source ∈ 𝓝 x :=
    hmd.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (f x))
  let V := (extChartAt I x).symm ⁻¹' (I.interior M ∩ f ⁻¹' (extChartAt I (f x)).source)
  have hV : V ∈ 𝓝 z := extChartAt_preimage_mem_nhds (inter_mem hi hs)
  have hFz : e z = extChartAt I (f x) (f x) := by
    change extChartAt I (f x) (f ((extChartAt I x).symm (extChartAt I x x))) = _
    rw [extChartAt_to_inv]
  have him : e '' V ∈ 𝓝 (extChartAt I (f x) (f x)) := hFz ▸ e.image_mem_nhds he hV
  have hp := (continuousAt_extChartAt (I := I) (f x)).preimage_mem_nhds him
  apply mem_of_superset (inter_mem (extChartAt_source_mem_nhds (I := I) (f x)) hp)
  rintro y ⟨hy, w, hw, hew⟩
  refine ⟨(extChartAt I x).symm w,hw.1,?_⟩
  have heq : extChartAt I (f x) (f ((extChartAt I x).symm w)) = extChartAt I (f x) y := hew
  exact (extChartAt I (f x)).injOn hw.2 hy heq

lemma image_interior_isOpen {f : M → N} (hf : IsSmoothEmbedding I I ∞ f) :
    IsOpen (f '' I.interior M) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x,hx,rfl⟩
  exact image_interior_mem_nhds hf hx

end CKSEmbeddingDerivative

end

end OAI
