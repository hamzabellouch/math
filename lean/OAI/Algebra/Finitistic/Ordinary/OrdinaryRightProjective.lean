import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimodule
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.DFinsupp

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation
universe u v w

/-- The finite direct sum of actual projective terms is projective. -/
theorem finitePi_projective {R : Type u} [Ring R] {ι : Type v} [Fintype ι]
    (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
    [∀ i, Module.Projective R (V i)] : Module.Projective R (∀ i, V i) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R) (M := V))

open CategoryTheory
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

/-- The actual underlying right-B complex of the genuine dg bimodule. -/
abbrev underlyingRightComplex (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) :
    CochainComplex (ModuleCat.{u} Bᵐᵒᵖ) ℤ :=
  ((ModuleCat.restrictScalars
    (Algebra.TensorProduct.includeRight (R := k) (A := B) (B := Bᵐᵒᵖ)).toRingHom).mapHomologicalComplex (.up ℤ)).obj P

theorem ordinaryO_right_projective (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ)
    (a : ℤ) (l : ℕ)
    [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)] :
    Module.Projective Bᵐᵒᵖ (BimoduleO P a l) := by
  let V : Fin (l+1) → Type u := fun i => (underlyingRightComplex P).X (a+(i.val:ℤ))
  have : Module.Projective Bᵐᵒᵖ (∀ i, V i) := finitePi_projective V
  exact Module.Projective.of_equiv (show (∀ i, V i) ≃ₗ[Bᵐᵒᵖ] BimoduleO P a l from LinearEquiv.refl _ _)
end LittleFinitistic.OrdinarySimulation

end

end OAI
