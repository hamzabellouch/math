import OAI.GroupTheory.PolycyclicRecognition.Algebra.KernelLinearSplitting
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ManifoldLocalCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieProductDifferential

namespace OAI

/-! # Local multiplication coordinates for an integrated height kernel

The kernel inclusion and a normalized height section have complementary
actual differentials. Their product map is therefore a local coordinate
map at the identity, by the ordinary inverse function theorem.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Manifold Topology ContDiff

variable {EN E W N G : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace N] [ChartedSpace EN N] [IsManifold (𝓘(ℝ, EN)) ∞ N]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

theorem kernel_product_local_coordinates
    (f : N → G) (s : W → G) (n : N)
    (hf : ContMDiff (𝓘(ℝ, EN)) (𝓘(ℝ, E)) ∞ f)
    (hs : ContMDiff (𝓘(ℝ, W)) (𝓘(ℝ, E)) ∞ s)
    (hf1 : f n = 1) (hs0 : s 0 = 1)
    (j : EN →L[ℝ] E) (d : E →L[ℝ] W) (l : W →L[ℝ] E)
    (hfj : HasMFDerivAt (𝓘(ℝ, EN)) (𝓘(ℝ, E)) f n j)
    (hsl : HasMFDerivAt (𝓘(ℝ, W)) (𝓘(ℝ, E)) s 0 l)
    (hj : Function.Injective j)
    (hrange : LinearMap.range j.toLinearMap = LinearMap.ker d.toLinearMap)
    (hdl : d.comp l = ContinuousLinearMap.id ℝ W) :
    (∃ U ∈ 𝓝 (n, (0 : W)), InjOn (fun p : N × W => f p.1 * s p.2) U) ∧
      map (fun p : N × W => f p.1 * s p.2) (𝓝 (n, (0 : W))) = 𝓝 (1 : G) := by
  let D : (EN × W) ≃L[ℝ] E :=
    (LinearEquiv.ofBijective (j.coprod l).toLinearMap
      (kernel_coprod_bijective j d l hj hrange hdl)).toContinuousLinearEquiv
  have hD : D.toContinuousLinearMap = j.coprod l := rfl
  have hfst : HasMFDerivAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, W))) (𝓘(ℝ, EN))
      Prod.fst (n, (0 : W)) (ContinuousLinearMap.fst ℝ EN W) := hasMFDerivAt_fst (n, (0 : W))
  have hsnd : HasMFDerivAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, W))) (𝓘(ℝ, W))
      Prod.snd (n, (0 : W)) (ContinuousLinearMap.snd ℝ EN W) := hasMFDerivAt_snd (n, (0 : W))
  have hp := PolycyclicRecognition.HasMFDerivAt.mul_at_one
    (hfj.comp (n, (0 : W)) hfst) (hsl.comp (n, (0 : W)) hsnd) hf1 hs0
  have hprod : HasMFDerivAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, W))) (𝓘(ℝ, E))
      (fun p : N × W => f p.1 * s p.2) (n, (0 : W)) D.toContinuousLinearMap := by
    rw [hD]
    apply hp.congr_mfderiv
    exact ContinuousLinearMap.comp_fst_add_comp_snd j l
  have hsmooth : ContMDiffAt ((𝓘(ℝ, EN)).prod (𝓘(ℝ, W))) (𝓘(ℝ, E)) ∞
      (fun p : N × W => f p.1 * s p.2) (n, (0 : W)) := by
    exact ((hf.comp contMDiff_fst).mul (hs.comp contMDiff_snd)).contMDiffAt
  simpa only [hf1, hs0, mul_one] using
    locally_injective_open_of_manifold_mfderiv_equiv D
      (by ext p; simp) hsmooth hprod

end PolycyclicRecognition

end

end OAI
