import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieExponential
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

namespace OAI

/-! # The derivative of a smooth intrinsic exponential at zero -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]

/- Directional derivatives along linear curves determine the full derivative
of an already smooth map. -/
omit [FiniteDimensional ℝ E] [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G] in
theorem hasMFDerivAt_zero_of_smooth_linear_curves
    {f : E → G} (d : E →L[ℝ] E)
    (hs : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ f 0)
    (hc : ∀ v : E, HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,E))
      (fun t : ℝ => f (t • v)) 0
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (d v))) :
    HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) f 0 d := by
  have hd := (hs.mdifferentiableAt (by simp)).hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro v
  change E at v
  let line : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v
  have hl : HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,E)) (fun t : ℝ => t • v) 0 line :=
    line.hasMFDerivAt
  have hs' : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ f ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact hs
  have hh := (hs'.mdifferentiableAt (by simp)).hasMFDerivAt.comp (0 : ℝ) hl
  have he := congrArg (fun k : ℝ →L[ℝ] E => k 1) (hasMFDerivAt_unique hh (hc v))
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f ((0 : ℝ) • v)) ((1 : ℝ) • v) = (1 : ℝ) • d v at he
  have he' : (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f ((0 : ℝ) • v)) v = d v := by
    simpa only [one_smul] using he
  have hz := congrArg (fun z : E => (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) f z) v) (zero_smul ℝ v)
  exact hz.symm.trans he'

omit [FiniteDimensional ℝ E] [LieGroup (𝓘(ℝ,E)) ⊤ G] in
theorem IsGroupExponential.hasMFDerivAt_zero_of_smooth
    {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G} (hExp : IsGroupExponential Exp)
    (hs : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (fun x : E => Exp x) 0) :
    HasMFDerivAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun x : E => Exp x) 0
      (ContinuousLinearMap.id ℝ E) := by
  have hd := (hs.mdifferentiableAt (by simp)).hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro v
  change E at v
  let line : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) v
  have hl : HasMFDerivAt (𝓘(ℝ,ℝ)) (𝓘(ℝ,E)) (fun t : ℝ => t • v) 0 line :=
    line.hasMFDerivAt
  have hs' : ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞ (fun x : E => Exp x) ((0 : ℝ) • v) := by
    rw [zero_smul]
    exact hs
  have hc := (hs'.mdifferentiableAt (by simp)).hasMFDerivAt.comp (0 : ℝ) hl
  have he := hasMFDerivAt_unique hc (hExp.hasMFDerivAt_zero v)
  have hev := congrArg (fun f : ℝ →L[ℝ] E => f 1) he
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun x : E => Exp x) ((0 : ℝ) • v))
    ((1 : ℝ) • v) = (1 : ℝ) • v at hev
  have hev' : (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun x : E => Exp x) ((0 : ℝ) • v)) v = v := by
    simpa only [one_smul] using hev
  have hz := congrArg (fun z : E =>
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (fun x : E => Exp x) z) v) (zero_smul ℝ v)
  exact hz.symm.trans hev'

end PolycyclicRecognition

end

end OAI
