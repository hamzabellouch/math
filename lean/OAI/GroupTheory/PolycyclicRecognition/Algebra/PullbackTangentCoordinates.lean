import OAI.GroupTheory.PolycyclicRecognition.Geometry.TransportedManifold
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ChartedVectorFieldBracket

namespace OAI

/-! # Tangent coordinates of the explicit pulled-back atlas -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace X] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem mfderiv_pullback (e : X ≃ₜ M) (x : X) :
    letI : ChartedSpace E X := pullbackChartedSpace (E := E) e
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e x = ContinuousLinearMap.id ℝ E := by
  let : ChartedSpace E X := pullbackChartedSpace (E := E) e
  let : IsManifold (𝓘(ℝ,E)) ∞ X := pullback_isManifold (E := E) e
  have he := (contMDiff_pullback (E := E) e).mdifferentiableAt (x := x) (by simp)
  have hc : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E))
      (extChartAt (𝓘(ℝ,E)) (e x)) (e x) :=
    (show ContMDiffAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞
      (extChartAt (𝓘(ℝ,E)) (e x)) (e x) from contMDiffAt_extChartAt).mdifferentiableAt (by simp)
  have hm := mfderiv_comp x hc he
  have hchart : (extChartAt (𝓘(ℝ,E)) (e x)) ∘ e = extChartAt (𝓘(ℝ,E)) x := by
    funext y
    rfl
  erw [hchart,mfderiv_extChartAt_self,mfderiv_extChartAt_self,
    ContinuousLinearMap.id_comp] at hm
  exact hm.symm

theorem mfderiv_pullback_symm (e : X ≃ₜ M) (y : M) :
    letI : ChartedSpace E X := pullbackChartedSpace (E := E) e
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e.symm y = ContinuousLinearMap.id ℝ E := by
  let : ChartedSpace E X := pullbackChartedSpace (E := E) e
  let : IsManifold (𝓘(ℝ,E)) ∞ X := pullback_isManifold (E := E) e
  have he := (contMDiff_pullback (E := E) e).mdifferentiableAt
    (x := e.symm y) (by simp)
  have hi := (contMDiff_pullback_symm (E := E) e).mdifferentiableAt
    (x := y) (by simp)
  have hh := mfderiv_comp (I' := 𝓘(ℝ,E)) y he hi
  have hfun : e ∘ e.symm = (id : M → M) := by
    funext z
    exact e.apply_symm_apply z
  rw [hfun,mfderiv_id] at hh
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun A : E →L[ℝ] E => A v) hh
  change v = (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e (e.symm y))
    ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e.symm y) v) at hv
  rw [mfderiv_pullback] at hv
  exact hv.symm

end PolycyclicRecognition

end

end OAI
