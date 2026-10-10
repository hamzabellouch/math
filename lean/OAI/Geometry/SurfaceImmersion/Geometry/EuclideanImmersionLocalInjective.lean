import OAI.Geometry.SurfaceImmersion.Atlas.SurfaceChartRepresentative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! A smooth finite-dimensional immersion is locally injective, using
an actual linear left inverse followed by the inverse function theorem. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem euclidean_immersion_locally_injective {f : Base → ProjectionTarget 3}
    (hf : ContDiff ℝ ∞ f) (p : Base) (hp : Function.Injective (fderiv ℝ f p)) :
    ∃ U : Set Base, IsOpen U ∧ p ∈ U ∧ U.InjOn f := by
  let L := fderiv ℝ f p
  obtain ⟨A,hA⟩ := L.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hp)
  let P : ProjectionTarget 3 →L[ℝ] Base := A.toContinuousLinearMap
  have hPL : P.comp L = ContinuousLinearMap.id ℝ Base := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun T : Base →ₗ[ℝ] Base => T v) hA
  let g := P ∘ f
  have hg : ContDiff ℝ ∞ g := P.contDiff.comp hf
  have hd : HasFDerivAt g (ContinuousLinearEquiv.refl ℝ Base).toContinuousLinearMap p := by
    have h := P.hasFDerivAt.comp p (hf.differentiable (by simp) p).hasFDerivAt
    change HasFDerivAt g (P.comp L) p at h
    rw [hPL] at h
    exact h
  let e := hg.contDiffAt.toOpenPartialHomeomorph g hd (by simp)
  refine ⟨e.source,e.open_source,hg.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp),?_⟩
  intro x hx y hy hxy
  apply e.injOn hx hy
  exact congrArg P hxy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
