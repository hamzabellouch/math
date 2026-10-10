import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

namespace OAI

namespace Yau.Geometry
open Bundle Manifold ContinuousLinearMap
open scoped ContDiff Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def bilinearPullback (B : W →L[ℝ] W →L[ℝ] ℝ) (T : F →L[ℝ] W) :
    F →L[ℝ] F →L[ℝ] ℝ := (T.precomp ℝ).comp (B.comp T)

lemma bilinearPullback_apply (B : W →L[ℝ] W →L[ℝ] ℝ) (T : F →L[ℝ] W) (v w : F) :
    bilinearPullback B T v w = B (T v) (T w) := rfl

lemma smooth_bilinear_pullback (B : M → W →L[ℝ] W →L[ℝ] ℝ)
    (T : ∀ x, V x →L[ℝ] W)
    (hB : ContMDiff I 𝓘(ℝ,W →L[ℝ] W →L[ℝ] ℝ) ∞ B)
    (hT : ContMDiff I (I.prod 𝓘(ℝ,F →L[ℝ] W)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] W)
        (E := fun x ↦ V x →L[ℝ] Bundle.Trivial M W x) x (T x))) :
    ContMDiff I (I.prod 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ V x →L[ℝ] V x →L[ℝ] ℝ) x
        (bilinearPullback (B x) (T x))) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id,?_⟩
  have ht := ((contMDiffAt_hom_bundle _).mp (hT x)).2
  let t : M → F →L[ℝ] W := fun y ↦
    (T y).comp ((trivializationAt F V x).symmL ℝ y)
  have ht' : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] W) ∞ t x := by
    simpa [inCoordinates, t] using ht
  have hBT : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] W →L[ℝ] ℝ) ∞
      (fun y ↦ (B y).comp (t y)) x :=
    (hB x).clm_comp ht'
  have hpre : ContMDiffAt I 𝓘(ℝ,(W →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun y ↦ (t y).precomp ℝ) x :=
    ht'.clm_precomp
  have hh : ContMDiffAt I 𝓘(ℝ,F →L[ℝ] F →L[ℝ] ℝ) ∞
      (fun y ↦ ((t y).precomp ℝ).comp ((B y).comp (t y))) x :=
    hpre.clm_comp hBT
  apply hh.congr_of_eventuallyEq
  filter_upwards [(trivializationAt F V x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F V x)] with y hy
  ext v w
  rw [inCoordinates_apply_eq₂ hy hy (Set.mem_univ _)]
  simp [bilinearPullback,t,Trivialization.symmL_apply,hy]

end
end Yau.Geometry

end OAI
