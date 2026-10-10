import OAI.Geometry.NodalSets.Elliptic.SmoothBilinearPullback

namespace OAI

namespace Yau.Geometry
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V W : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [TopologicalSpace (TotalSpace G W)] [FiberBundle G W] [VectorBundle ℝ G W]

lemma smooth_bundle_inverse (T : ∀ x, V x ≃L[ℝ] W x)
    (hT : ContMDiff I (I.prod 𝓘(ℝ,F →L[ℝ] G)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x
        (T x).toContinuousLinearMap)) :
    ContMDiff I (I.prod 𝓘(ℝ,G →L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (G →L[ℝ] F) (E := fun x ↦ W x →L[ℝ] V x) x
        (T x).symm.toContinuousLinearMap) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,?_⟩
  have ht := ((contMDiffAt_hom_bundle _).mp (hT x)).2
  let t := fun y ↦ inCoordinates F V G W x y x y (T y).toContinuousLinearMap
  have ht' : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] G) ∞ t x := ht
  have hi : (t x).IsInvertible := by
    dsimp only [t]
    rw [inCoordinates_eq (mem_baseSet_trivializationAt F V x)
      (mem_baseSet_trivializationAt G W x)]
    exact ⟨(((trivializationAt F V x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt F V x)).symm.trans (T x)).trans
      ((trivializationAt G W x).continuousLinearEquivAt ℝ x
      (mem_baseSet_trivializationAt G W x)),rfl⟩
  apply (hi.contDiffAt_map_inverse.comp_contMDiffAt ht').congr_of_eventuallyEq
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x),
    (trivializationAt G W x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt G W x)] with y hy hz
  dsimp only [Function.comp_def]
  dsimp only [t]
  rw [inCoordinates_eq hy hz,inCoordinates_eq hz hy]
  simp only [inverse_equiv_comp,inverse_comp_equiv,inverse_equiv,ContinuousLinearEquiv.symm_symm]
  rfl

end
end Yau.Geometry

end OAI
