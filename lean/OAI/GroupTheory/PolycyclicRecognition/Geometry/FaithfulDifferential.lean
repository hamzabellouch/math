import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponentialNaturality
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialTangentUniqueness

namespace OAI

/-! # A faithful group representation has faithful differential

If two tangent vectors have the same image, their represented one-parameter
subgroups agree. Faithfulness of the representation and uniqueness of the
tangent vector then identify the two vectors. No immersion theorem or global
injectivity of the Lie exponential is required.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem injective_algebra_differential
    {Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G} (hExp : IsGroupExponential Exp)
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →L[ℝ] A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1 j) :
    Function.Injective j := by
  intro v w hvw
  apply hExp.eq_of_oneParameter_eq
  intro t
  apply hρ
  rw [hom_exp_eq_algebraExpUnit hExp ρ j hd,
    hom_exp_eq_algebraExpUnit hExp ρ j hd, map_smul, map_smul, hvw]

end PolycyclicRecognition

end

end OAI
