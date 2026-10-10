import OAI.GroupTheory.PolycyclicRecognition.Geometry.LocalParameterSmoothness
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Recovering smoothness through an injective differential

Only the finite-dimensional vector-space target needed for exponential
coordinates is used. A linear left inverse followed by the ordinary inverse
function theorem supplies the local smooth inverse along the image.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Manifold Topology ContDiff

variable {E V A M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [TopologicalSpace M] [ChartedSpace E M]

theorem contMDiffAt_of_comp_of_injective_differential
    {f : M → V} {F : V → A} {x : M} {D : V →L[ℝ] A}
    (hf : ContinuousAt f x) (hF : ContDiffAt ℝ ∞ F (f x))
    (hD : HasFDerivAt F D (f x)) (hDi : Function.Injective D)
    (hcomp : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) ∞ (F ∘ f) x) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ f x := by
  obtain ⟨p, hp⟩ := D.toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hDi)
  let q : A →L[ℝ] V := p.toContinuousLinearMap
  have hqD : q.comp D = ContinuousLinearMap.id ℝ V := by
    ext v
    exact DFunLike.congr_fun hp v
  let P : V → V := q ∘ F
  have hP : ContDiffAt ℝ ∞ P (f x) := q.contDiff.contDiffAt.comp (f x) hF
  let d : V ≃L[ℝ] V := ContinuousLinearEquiv.refl ℝ V
  have hPd : HasFDerivAt P d.toContinuousLinearMap (f x) := by
    change HasFDerivAt P (ContinuousLinearMap.id ℝ V) (f x)
    rw [← hqD]
    exact q.hasFDerivAt.comp (f x) hD
  let r : V → V := hP.localInverse hPd (by simp)
  have hr : ContDiffAt ℝ ∞ r (P (f x)) := hP.to_localInverse hPd (by simp)
  have hleft : ∀ᶠ y in 𝓝 (f x), r (P y) = y :=
    (hP.hasStrictFDerivAt' hPd (by simp)).eventually_left_inverse
  have hqcomp : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ (P ∘ f) x :=
    q.contDiff.contMDiff.contMDiffAt.comp x hcomp
  have hres : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, V)) ∞ (r ∘ P ∘ f) x :=
    hr.contMDiffAt.comp x hqcomp
  apply hres.congr_of_eventuallyEq
  filter_upwards [hf.tendsto.eventually hleft] with y hy
  exact hy.symm

end PolycyclicRecognition

end

end OAI
