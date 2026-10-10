import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialProductCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepresentationParameterChart
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential

namespace OAI

/-! # An analytic represented chart from two exponential parameters -/

noncomputable section
namespace PolycyclicRecognition
open scoped ContDiff

variable {G E A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

omit [IsTopologicalGroup G] in
theorem representedLocalChart_of_exponential_parameter
    (ρ : G →* Aˣ) (p : OpenPartialHomeomorph E G)
    (hp : (0 : E) ∈ p.source) (hp0 : p 0 = 1)
    (K D : E →L[ℝ] A) (hinj : Function.Injective (K + D))
    (he : ∀ x ∈ p.source, ρ (p x) = algebraExpUnit (K x) * algebraExpUnit (D x)) :
    Nonempty (RepresentedLocalChart (E := E) ρ) := by
  obtain ⟨P,hP⟩ := exists_projected_exponential_coordinates K D hinj
  let U : E → A := fun x => NormedSpace.exp (K x) * NormedSpace.exp (D x)
  let V : E → A := fun x => NormedSpace.exp (-D x) * NormedSpace.exp (-K x)
  have hU : ContDiff ℝ ω U :=
    (contDiff_algebra_exp.comp K.contDiff).mul (contDiff_algebra_exp.comp D.contDiff)
  have hV : ContDiff ℝ ω V :=
    (contDiff_algebra_exp.comp D.contDiff.neg).mul (contDiff_algebra_exp.comp K.contDiff.neg)
  apply representedLocalChart_of_parameter ρ p hp hp0 P U V hU hV _ _ hP
  · intro x hx
    rw [he x hx]
    rfl
  · intro x hx
    rw [he x hx, mul_inv_rev]
    rfl

omit [IsTopologicalGroup G] in
theorem representedLocalChart_of_exponential_localization
    (ρ : G →* Aˣ) (f : E → G) (K D : E →L[ℝ] A)
    (hinj : Function.Injective (K + D))
    (he : ∀ x, ρ (f x) = algebraExpUnit (K x) * algebraExpUnit (D x))
    (hl : ∃ p : OpenPartialHomeomorph E G, (0 : E) ∈ p.source ∧ p 0 = 1 ∧
      ∀ x ∈ p.source, p x = f x) :
    Nonempty (RepresentedLocalChart (E := E) ρ) := by
  obtain ⟨p,hp,hp0,hpf⟩ := hl
  exact representedLocalChart_of_exponential_parameter ρ p hp hp0 K D hinj
    (fun x hx => (congrArg ρ (hpf x hx)).trans (he x))

end PolycyclicRecognition

end

end OAI
