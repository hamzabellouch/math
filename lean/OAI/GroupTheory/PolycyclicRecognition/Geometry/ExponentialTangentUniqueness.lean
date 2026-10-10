import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieConjugationDifferential

namespace OAI

/-! # Recovering tangent vectors from exponential curves -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ⊤ G]

omit [LieGroup (𝓘(ℝ, E)) ⊤ G] in
theorem IsGroupExponential.eq_of_oneParameter_eq
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    {v w : GroupLieAlgebra (𝓘(ℝ, E)) G}
    (h : ∀ t : ℝ, Exp (t • v) = Exp (t • w)) : v = w := by
  have hw := hExp.hasMFDerivAt_zero w
  rw [← funext h] at hw
  have hd := hasMFDerivAt_unique (hExp.hasMFDerivAt_zero v) hw
  have he := congrArg (fun D : ℝ →L[ℝ] E => D 1) hd
  change (1 : ℝ) • (v : E) = (1 : ℝ) • (w : E) at he
  simpa only [one_smul] using he

/-- An exponential-compatible linear action is the actual tangent action;
global injectivity of the exponential is not required. -/
theorem conjugationDifferential_eq_of_exponential [T2Space G]
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (g : G) (A : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ[ℝ] GroupLieAlgebra (𝓘(ℝ, E)) G)
    (hA : ∀ v, Exp (A v) = g * Exp v * g⁻¹) :
    ∀ v, conjugationDifferentialHom g v = A v := by
  intro v
  apply hExp.eq_of_oneParameter_eq
  intro t
  calc
    Exp (t • conjugationDifferentialHom g v) =
        Exp (conjugationDifferentialHom g (t • v)) := by rw [map_smul]
    _ = g * Exp (t • v) * g⁻¹ := (conjugation_exponential hExp g (t • v)).symm
    _ = Exp (A (t • v)) := (hA (t • v)).symm
    _ = Exp (t • A v) := by rw [map_smul]

end PolycyclicRecognition

end

end OAI
