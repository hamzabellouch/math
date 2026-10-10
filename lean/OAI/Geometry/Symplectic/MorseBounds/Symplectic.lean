import Mathlib

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.Geometry
open scoped Manifold ContDiff
noncomputable section

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev SmoothModel (n : ℕ) := 𝓘(ℝ, Model n)

section Definitions
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Model n) M]

abbrev TwoForm := (x : M) →
  TangentSpace (SmoothModel n) x →L[ℝ] TangentSpace (SmoothModel n) x →L[ℝ] ℝ

noncomputable def chartTwoForm (w : TwoForm (n := n) (M := M)) (x : M)
    (y : Model n) : Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  let c := extChartAt (SmoothModel n) x
  let dc := (mfderiv (SmoothModel n) (SmoothModel n) c.symm y).comp
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.toContinuousLinearMap
  (ContinuousLinearMap.precomp ℝ dc).comp ((w (c.symm y)).comp dc)

structure SymplecticForm where
  form : TwoForm (n := n) (M := M)
  alternating : ∀ x v, form x v v = 0
  nondegenerate : ∀ x, Function.Injective (form x)
  smooth : ∀ x, ContDiffOn ℝ ∞ (chartTwoForm form x)
    (extChartAt (SmoothModel n) x).target
  closed : ∀ x y, y ∈ (extChartAt (SmoothModel n) x).target →
    ∀ u v w : Model n,
      fderiv ℝ (chartTwoForm form x) y u v w +
      fderiv ℝ (chartTwoForm form x) y v w u +
      fderiv ℝ (chartTwoForm form x) y w u v = 0

end Definitions
end
end MorseArnold.Geometry

end

end OAI
