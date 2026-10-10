import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothManifoldImmersionCancellation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AutomaticSmoothAlgebraHom

namespace OAI

/-! # Testing smoothness in faithful group coordinates

An injective differential at the identity suffices to test smoothness:
translate to the identity and apply local chart cancellation.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {EN EG N G A : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
  [TopologicalSpace N] [ChartedSpace EN N]
  [TopologicalSpace G] [ChartedSpace EG G] [Group G]
  [IsTopologicalGroup G] [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

theorem contMDiffAt_of_unitsHom_injective_differential
    (ρ : G →* Aˣ)
    (hρ : ContMDiff (𝓘(ℝ, EG)) (𝓘(ℝ, A)) ∞ (fun g => (ρ g : A)))
    (D : EG →L[ℝ] A)
    (hD : HasMFDerivAt (𝓘(ℝ, EG)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1 D)
    (hDi : Function.Injective D)
    {f : N → G} {x : N} (hf : ContinuousAt f x)
    (hcomp : ContMDiffAt (𝓘(ℝ, EN)) (𝓘(ℝ, A)) ∞ (fun y => (ρ (f y) : A)) x) :
    ContMDiffAt (𝓘(ℝ, EN)) (𝓘(ℝ, EG)) ∞ f x := by
  let g := f x
  let f' : N → G := fun y => g⁻¹ * f y
  let F : G → A := fun z => (ρ z : A)
  have hf' : ContinuousAt f' x := continuousAt_const.mul hf
  have hz : f' x = 1 := inv_mul_cancel g
  have hF' : ContMDiffAt (𝓘(ℝ, EG)) (𝓘(ℝ, A)) ∞ F (f' x) := by
    rw [hz]
    exact hρ 1
  have hD' : HasMFDerivAt (𝓘(ℝ, EG)) (𝓘(ℝ, A)) F (f' x) D := by
    rw [hz]
    exact hD
  have hc : ContMDiffAt (𝓘(ℝ, EN)) (𝓘(ℝ, A)) ∞ (F ∘ f') x := by
    have h := (ContinuousLinearMap.mul ℝ A (ρ g⁻¹ : A)).contDiff.contMDiff.contMDiffAt.comp
      x hcomp
    have heq : (fun y => (ρ g⁻¹ : A) * (ρ (f y) : A)) = F ∘ f' := by
      funext y
      simp only [Function.comp_apply, F, f', map_mul, Units.val_mul]
    change ContMDiffAt (𝓘(ℝ, EN)) (𝓘(ℝ, A)) ∞
      (fun y => (ρ g⁻¹ : A) * (ρ (f y) : A)) x at h
    rwa [heq] at h
  have hs := contMDiffAt_of_comp_of_injective_mfderiv hf' hF' hD' hDi hc
  have hout := (contMDiff_mul_left (I := 𝓘(ℝ, EG)) (a := g)).contMDiffAt.comp x hs
  have heq : (fun z => g * z) ∘ f' = f := by
    funext y
    exact mul_inv_cancel_left g (f y)
  rwa [heq] at hout

end PolycyclicRecognition

end

end OAI
