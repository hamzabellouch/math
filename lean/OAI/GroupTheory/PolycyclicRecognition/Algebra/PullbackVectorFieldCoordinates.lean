import OAI.GroupTheory.PolycyclicRecognition.Algebra.PullbackTangentCoordinates

namespace OAI

/-! # Vector fields in the pulled-back atlas -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E M X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [TopologicalSpace X] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ,E)) ∞ M]

theorem chartVectorField_pullback (e : X ≃ₜ M) (x : X) :
    letI : ChartedSpace E X := pullbackChartedSpace (E := E) e
    ∀ (V : (p : X) → TangentSpace (𝓘(ℝ,E)) p) (y : E),
      y ∈ (extChartAt (𝓘(ℝ,E)) (e x)).target →
      chartVectorField x V y =
        chartVectorField (e x) (fun g => V (e.symm g)) y := by
  let : ChartedSpace E X := pullbackChartedSpace (E := E) e
  let : IsManifold (𝓘(ℝ,E)) ∞ X := pullback_isManifold (E := E) e
  intro V y hy
  let φ := extChartAt (𝓘(ℝ,E)) (e x)
  let ψ := extChartAt (𝓘(ℝ,E)) x
  have hfun : ψ.symm = e.symm ∘ φ.symm := rfl
  have hi : MDifferentiableAt (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ.symm y := by
    simpa only [φ,mfld_simps,mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hy
  have he := (contMDiff_pullback_symm (E := E) e).mdifferentiableAt
    (x := φ.symm y) (by simp)
  have hd := mfderiv_comp (I' := 𝓘(ℝ,E)) y he hi
  rw [← hfun] at hd
  have hD : (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ψ.symm y : E →L[ℝ] E) =
      mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ.symm y := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun A : E →L[ℝ] E => A v) hd
    change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ψ.symm y) v =
      (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) e.symm (φ.symm y))
        ((mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ.symm y) v) at hv
    rw [mfderiv_pullback_symm] at hv
    exact hv
  change (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) ψ.symm y).inverse (V (ψ.symm y)) =
    (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) φ.symm y).inverse (V (e.symm (φ.symm y)))
  rw [hD]
  rfl

end PolycyclicRecognition

end

end OAI
