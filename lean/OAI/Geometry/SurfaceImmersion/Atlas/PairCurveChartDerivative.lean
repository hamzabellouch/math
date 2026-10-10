import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairDerivative
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! Injectivity of the paired curve velocity is invariant under the
actual two surface charts. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem paired_curve_derivative_injective
    {A B : ℝ → M} {θ : ℝ → Base × Base} (x y : M) (t : ℝ)
    (hA : ContMDiffAt 𝓘(ℝ) planeModel ∞ A t)
    (hB : ContMDiffAt 𝓘(ℝ) planeModel ∞ B t)
    (hAx : A t ∈ (chart x).source) (hBy : B t ∈ (chart y).source)
    (hθ : ContDiffAt ℝ ∞ θ t)
    (he : θ =ᶠ[𝓝 t] fun s => (chart x (A s),chart y (B s)))
    (hinj : Function.Injective (fderiv ℝ θ t)) :
    Function.Injective ((mfderiv 𝓘(ℝ) planeModel A t).prod (mfderiv 𝓘(ℝ) planeModel B t)) := by
  have hx := ((chart_smooth x) (A t) hAx).contMDiffAt ((chart x).open_source.mem_nhds hAx)
  have hy := ((chart_smooth y) (B t) hBy).contMDiffAt ((chart y).open_source.mem_nhds hBy)
  have heA : (fun s => (θ s).1) =ᶠ[𝓝 t] (chart x) ∘ A := he.mono fun _ hs => congrArg Prod.fst hs
  have heB : (fun s => (θ s).2) =ᶠ[𝓝 t] (chart y) ∘ B := he.mono fun _ hs => congrArg Prod.snd hs
  have hdA : fderiv ℝ (fun s => (θ s).1) t =
      (mfderiv planeModel 𝓘(ℝ,Base) (chart x) (A t)).comp (mfderiv 𝓘(ℝ) planeModel A t) := by
    have h : mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (fun s => (θ s).1) t =
        mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) ((chart x) ∘ A) t := heA.mfderiv_eq
    rw [mfderiv_eq_fderiv,mfderiv_comp t (hx.mdifferentiableAt (by simp))
      (hA.mdifferentiableAt (by simp))] at h
    exact h
  have hdB : fderiv ℝ (fun s => (θ s).2) t =
      (mfderiv planeModel 𝓘(ℝ,Base) (chart y) (B t)).comp (mfderiv 𝓘(ℝ) planeModel B t) := by
    have h : mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) (fun s => (θ s).2) t =
        mfderiv 𝓘(ℝ) 𝓘(ℝ,Base) ((chart y) ∘ B) t := heB.mfderiv_eq
    rw [mfderiv_eq_fderiv,mfderiv_comp t (hy.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp))] at h
    exact h
  have hfst : fderiv ℝ (fun s => (θ s).1) t = ((ContinuousLinearMap.fst ℝ Base Base).comp (fderiv ℝ θ t)) :=
    (hθ.differentiableAt (by simp)).hasFDerivAt.fst.fderiv
  have hsnd : fderiv ℝ (fun s => (θ s).2) t = ((ContinuousLinearMap.snd ℝ Base Base).comp (fderiv ℝ θ t)) :=
    (hθ.differentiableAt (by simp)).hasFDerivAt.snd.fderiv
  intro a b hab
  apply hinj
  apply Prod.ext
  · change ((ContinuousLinearMap.fst ℝ Base Base).comp (fderiv ℝ θ t)) a = ((ContinuousLinearMap.fst ℝ Base Base).comp (fderiv ℝ θ t)) b
    rw [← hfst,hdA]
    exact congrArg (mfderiv planeModel 𝓘(ℝ,Base) (chart x) (A t)) (congrArg Prod.fst hab)
  · change ((ContinuousLinearMap.snd ℝ Base Base).comp (fderiv ℝ θ t)) a = ((ContinuousLinearMap.snd ℝ Base Base).comp (fderiv ℝ θ t)) b
    rw [← hsnd,hdB]
    exact congrArg (mfderiv planeModel 𝓘(ℝ,Base) (chart y) (B t)) (congrArg Prod.snd hab)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
