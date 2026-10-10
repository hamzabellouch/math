import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ScalarExtendedRepresentationFiniteness

namespace OAI

/-! # Rational specialization of scalar extension for integral representations -/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra TensorProduct
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ M]

abbrev rationalRepresentation (ρ : Representation ℤ G M) :
    Representation ℚ G (ℚ ⊗[ℤ] M) := scalarExtendedRepresentation ℚ ρ

@[simp] theorem rationalRepresentation_tmul (ρ : Representation ℤ G M)
    (g : G) (q : ℚ) (m : M) :
    rationalRepresentation ρ g (q ⊗ₜ[ℤ] m) = q ⊗ₜ[ℤ] ρ g m := rfl

theorem rationalRepresentation_finite (ρ : Representation ℤ G M)
    [Module.Finite ℤ[G] ρ.asModule] :
    Module.Finite ℚ[G] (rationalRepresentation ρ).asModule :=
  scalarExtendedRepresentation_finite ℚ ρ

end PolycyclicRecognition

end

end OAI
